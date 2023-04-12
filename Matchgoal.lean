import Std
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.Data.Json
import Matchgoal.Trace
import Matchgoal.LogicT

namespace MatchGoal

open Lean Elab Meta Tactic Term Std RBMap

-- TODO: Make naming consistent, choose between `Pattern` and `Unification`.

declare_syntax_cat goal_matcher
declare_syntax_cat hyp_matcher
declare_syntax_cat unification_var
declare_syntax_cat unification_expr

scoped syntax (name := var) "#" noWs ident : unification_var


/- Names that are created from `#<name>` syntax. -/
@[reducible]
def UnificationName := Name

-- macro_rules
-- | `(identifier| # $i:unification_var) => sorry

-- scoped syntax unification_var : term -- allow unification variables to be used in terms.

-- every unification variable is a term.
open Lean Elab in
scoped elab (name := var2term) t:unification_var : term => do
  let s : Syntax ←
    match t with
    | `(unification_var| #$i:ident) => pure i
    | _ => throwUnsupportedSyntax
  elabTerm s (expectedType? := .none)

-- 1. var -var2term-> term -term2expr-> expr
scoped syntax (name := term2expr) (priority := 0)
  term : unification_expr
scoped syntax (name := hyp)
  "(" unification_var ws ":" ws unification_expr ")" : hyp_matcher

scoped syntax (name := elabUnificationExpr)
  "[unification_expr|" unification_expr "]" : term
macro_rules
| `([unification_expr| $e:term]) => return e

syntax hyps := sepBy(hyp_matcher, "; ")

structure MVar where
  id: MVarId


instance : ToMessageData MVar where
  toMessageData mvar := toMessageData mvar.id

#check MetaM
open Lean Elab Meta Tactic in
def MVar.getName (mvar : MVar) : TacticM Name := do
  mvar.id.getTag

def MVar.assign (mvar : MVar) (e : Expr) : TacticM Unit :=
  mvar.id.assign e
def MVar.toExpr (mvar : MVar) : Expr := Expr.mvar mvar.id
def MVar.ofExpr: Expr → TacticM MVar
| .mvar id => return .mk id
| e => throwError "Internal tactic error: expected mvar, found expression {e}"

 -- TODO: try not to create more MVars?
open Lean Elab in
def MVar.toSyntax (mvar : MVar) : TermElabM Syntax := exprToSyntax mvar.toExpr

instance : Coe MVar Expr where
  coe := MVar.toExpr

structure PatternCtx where
  mvars : Std.HashMap Name MVar := {}
  hyps : Std.HashMap Name FVarId := {} -- match hypothesis pattern names to real hypothesis names.
deriving Inhabited

instance : ToMessageData PatternCtx where
  toMessageData pctx := Id.run do
    let mvars := MessageData.ofList <| pctx.mvars.toList.map (fun (k, v) =>  m!"{k} ↦ {v}")
    let hyps := MessageData.ofList <| pctx.hyps.toList.map fun (k, v) => m!"{k} ↦ {v.name}"
    m!"PatternCtx(tacticState?, {mvars}, {hyps})"


-- TODO: think about order of monads?
-- is it (LogicT TacticM) or (TacticT LogicM) ?
def MatchGoalM α := TacticM (List α)

def MatchGoalM.unwrap : MatchGoalM α → TacticM (List α) := id
def MatchGoalM.wrap : TacticM (List α) → MatchGoalM α := id

instance : Functor MatchGoalM where
  map f mas := MatchGoalM.wrap do return (← mas).map f

instance : Monad MatchGoalM where
  pure a := MatchGoalM.wrap (pure [a])
  bind mas a2mbs := MatchGoalM.wrap do
    let mut xs := []
    for a in (← mas.unwrap) do
      xs := xs.append (← a2mbs a)
    return xs

instance : MonadBacktrack Tactic.SavedState MatchGoalM where
  saveState := MatchGoalM.wrap <| do let s ← saveState; return [s]
  restoreState state := MatchGoalM.wrap <| do restoreState state; return [()]

instance : MonadLift TacticM MatchGoalM where
  monadLift ma := MatchGoalM.wrap do return [← ma]

instance : MonadRef MatchGoalM where
  getRef :=
    let I : MonadRef TacticM := inferInstance
    monadLift <| I.getRef
  withRef stx mxs := MatchGoalM.wrap do
    let I : MonadRef TacticM := inferInstance
    let xs ← mxs
    let xs ← xs.mapM (fun x => I.withRef stx (pure x))
    return xs

def foo : Int → Int → Int
| x, 0 | 0, x => 2 * x
| _ , _ => 42

instance : Alternative MatchGoalM where
  failure := MatchGoalM.wrap (return [])
  orElse  mas unit2mas := MatchGoalM.wrap do return (← mas) ++ (← unit2mas ())



def unificationVarFillHoles (s : TSyntax `unification_var) : StateT PatternCtx TacticM Syntax := do
  trace[matchgoal.debug.unify] m!"unifyV s:'{toString s}'?"
  match s with
  | `(unification_var| #$i:ident) | `(#$i:ident) => do -- TODO: should I match on 'unification_var' as well?
    trace[matchgoal.debug.unify] m!"unifyV s:'{toString s}'!"
    -- TODO: we might need to 'gensym' custom names here.
    if let .some fvar := (← get).hyps.find? i.getId
    then let I : Quote Name := inferInstance; return (I.quote fvar.name).raw

    match (← get).mvars.find? i.getId with
    | .some mvar => mvar.toSyntax
    | .none =>
        let mvar : MVar := ← MVar.ofExpr (← mkFreshExprMVar
            (type? := .none) (userName := i.getId) (kind := .natural))
        modify (fun ctx => { ctx with mvars := ctx.mvars.insert i.getId mvar })
        mvar.toSyntax
  | _ => throwUnsupportedSyntax


-- instantiate all unification variables in the expression and create a real Lean term.
-- Also update the state to recored new unification variables
-- TODO: how do I look inside a term and find unification variables?
open Lean Core Meta Elab Macro Tactic in
partial def unificationExprFillHoles (s : Syntax) : StateT PatternCtx TacticM Syntax := do
  trace[matchgoal.debug.unify] "s:'{toString s}'"
  match s with
  | `(term| $var:unification_var) => unificationVarFillHoles var
  | _ =>
    match s with
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s
    | Syntax.node info kind args =>
         return Syntax.node info kind (← args.mapM unificationExprFillHoles)

-- This needs to be refactored. We first fill the holes to get syntax with metavars
-- that everyone agrees on. Then we unify and backtrack.
-- open Lean Core Meta Elab Macro Tactic in
-- def runHypMatcher (ctx: PatternCtx) : TSyntax `hyp_matcher → MatchGoalM PatternCtx
-- | `(hyp_matcher| (#$i:ident : $e:unification_expr)) => do
--     ctx.restoreState
--     (← getMainDecl).lctx.decls.foldl (init := pure ctx) (fun mctx ldecl? => do
--       ctx.restoreState
--       match ldecl? with
--       | .none => return ctx
--       | .some ldecl => Alternative.orElse mctx (fun () => do
--         let ldeclType : Expr ← inferType ldecl.toExpr
--         let newctx ← unificationExprFillHoles ctx ldeclType e
--         newctx.saveState -- TODO: this should be un-necessary
--       ))
-- | _ => MatchGoalM.wrap <| throwUnsupportedSyntax


-- Substitute holes in the Syntax given by `unification_var` with the values in ctx
-- TODO: We need to know if we should substitute `MVars` or
-- `Name`s. In the hypothesis manipulation, we should substitute MVarIds.
-- For the final proof production, we should substitute `Names` ?
open Lean Elab Macro Tactic in
partial def substitute (ctx : PatternCtx) (s : Syntax) : TacticM Syntax := do
  trace[matchgoal.debug] "substitute s:'{toString s}'"
  match s with
  | `(unification_var| #$i:ident) | `(term| #$i:ident) => do
      -- Here we use the nasty trick of converting an `MVar` into a `Syntax` object.
      match (ctx.mvars.find? i.getId, ctx.hyps.find? i.getId) with
      | (.none, .none) => do
         logErrorAt s <|
           MessageData.tagged `Tactic.Matchgoal <|
           m!"Matchgoal variable {s} has not been unified. This is an error."
         return s
      | (.some mvar, .none) =>
         -- TODO: check that mvar has value?
         mvar.toSyntax
      | (.none, .some hyp) => do
           -- TODO: use `TSyntax` and not `Syntax`.
           let userName ← hyp.getUserName
           let I : Lean.Quote Name := inferInstance
           return (I.quote userName).raw -- Dose this actually work?
      | (.some _, .some v) => do
          logErrorAt s <|
             MessageData.tagged `Tactic.Matchgoal <|
             m!"Variable {s} is incorrectly used as a term variable and as a hypothesis variable '{v.name}'. This is an error."
          return s
  | _ =>
    match s with
    | Syntax.node info kind args => do return Syntax.node info kind (← args.mapM (substitute ctx))
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s


structure HypPattern where
  name : Name
  nameStx : TSyntax `ident -- for position information. -- TODO: create an abstraction.
  rhs : TSyntax `unification_expr

instance : ToMessageData HypPattern where
  toMessageData h := m!"{h.name} : {h.rhs}"



def HypPattern.parse : TSyntax `hyp_matcher →  TacticM HypPattern
| `(hyp_matcher| (#$i: ident : $e:unification_expr)) =>
   return { name := i.getId, nameStx := i, rhs := e }
| stx => do
  logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal <| m! "unknown hypothesis pattern '{stx}'"
  throwUnsupportedSyntax


def MatchGoalM.branch (xs : List (MatchGoalM α)) : MatchGoalM α :=
  MatchGoalM.wrap do
    let mut vs := []
    for x in xs do
      vs := vs ++ (← MatchGoalM.unwrap x)
    return vs

#check intro1P
#check MetaM

open Lean Core Elab Meta Macro Tactic in
def HypPattern.unify (pctx: PatternCtx) (hpat : HypPattern) (ldecl: LocalDecl) : TacticM (Option PatternCtx) := do
    let ldeclType : Expr ← inferType ldecl.toExpr
    trace[matchgoal.debug.unify] "HypPattern.unify {pctx} : {hpat} =?= {ldeclType}"
    -- | TODO: refactor code duplication
    let (hpatfilled, newctx) ← (unificationExprFillHoles hpat.rhs.raw).run pctx
    let hpatfilled : TSyntax `unification_expr := ⟨hpatfilled⟩
    let hpatfilledterm ←  monadLift (m := TacticM) <| `([unification_expr| $hpatfilled])
    let hpatexpr ← Tactic.elabTerm hpatfilledterm (expectedType? := .none)
    if ← isDefEq hpatexpr ldeclType
    then do
        trace[matchgoal.debug.unify] "SUCCESS: HypPattern.unify {pctx} : {hpat} === {ldeclType}"
        let hypMVar : Expr ← mkFreshExprMVar (type? := .none) (userName := hpat.name)
        let hypMVar : MVar ← MVar.ofExpr hypMVar
        hypMVar.assign hpatexpr
        -- TODO: ask Henrik if this is the optimal way.
        -- Convert the given goal `Ctx |- target` into `Ctx |- type -> target`.
        let newgoal ← (← getMainGoal).assert hpat.name ldeclType hpatexpr
        -- `intros` the arrow.
        let (hypFVar, newgoal) ← newgoal.intro1P
        replaceMainGoal [newgoal]
        pure (.some { pctx with hyps := pctx.hyps.insert hpat.name hypFVar })
    else
      trace[matchgoal.debug.unify] "FAILURE: HypPattern.unify {pctx} : {hpat} =!= {ldeclType}"
      return .none


/-- match goal tactic -/
-- TODO: why does 'local syntax' not work?
-- local syntax (name := matchgoal)
scoped syntax (name := matchgoal)
  "matchgoal" ws
  (hyps ws)?
  "⊢" ws (( unification_expr)? <|>  "_") ws "=>" ws tactic : tactic


open Lean Core Meta Elab Macro Tactic in
/-- The search state of the backtracking depth first search. -/
def depthFirstSearchHyps
  (tac : TSyntax `tactic)
  (hyppats : List HypPattern)
  (ctx : PatternCtx) : TacticM Bool :=  do
  match hyppats with
  | [] => do
      trace[matchgoal.debug.search] m!"substituting into '{tac}' from context {ctx}" -- TODO: make {ctx} nested
      let tac ← substitute ctx tac
      trace[matchgoal.debug.search] m!"running tactic '{tac}'."
      match ← tryTactic? (evalTactic tac) with
      | .some () =>
         trace[matchgoal.debug.search] m!"SUCCESS running '{tac}'."
         return true
      | _ =>
        trace[matchgoal.debug.search] m!"FAILURE running '{tac}'."
        return false
  | hyppat :: hyppats' =>
     let stateBeforeUnif ← Tactic.saveState
     for hyp in (← getMainDecl).lctx do
       if hyp.isImplementationDetail then continue
       stateBeforeUnif.restore -- bring back state before unifying.
       if let .some ctx'  ← hyppat.unify ctx hyp then
         if  (← depthFirstSearchHyps tac hyppats' ctx')
         then return true
     stateBeforeUnif.restore
     return False

open Lean Core Meta Elab Macro Tactic in
@[tactic MatchGoal.matchgoal]
def evalMatchgoal : Tactic := fun stx => -- (stx -> TacticM Unit)
  match stx with
  | `(tactic| matchgoal
        $[ $[ $hs? ];* ]?
        ⊢ _ => $t ) => do
        return ()

  | `(tactic| matchgoal
      $[ $[ $hpatstxs? ];* ]?
      ⊢ $[ $gpat?:unification_expr ]? => $tac ) => do
    trace[matchgoal.debug] m!"{toString gpat?}"
    let mut ctx : PatternCtx := default
    if let .some gpat := gpat? then
      let (gpatfilled, ctx') ← (unificationExprFillHoles gpat).run default
      let gpatfilled : TSyntax `unification_expr := ⟨gpatfilled⟩
      ctx := ctx' -- Lean does not have nice syntax to shadow
      let gpatfilledterm ←  monadLift (m := TacticM) <| `([unification_expr| $gpatfilled])
      let gpatexpr ← Tactic.elabTerm gpatfilledterm (expectedType? := .none)
      if not (← isDefEq gpatexpr (← getMainTarget)) then
       logErrorAt gpat
         <| MessageData.tagged `Tactic.Matchgoal <| m! "unable to unify goal pattern {gpatexpr} with goal {← getMainTarget}"
    -- We have now unified goal, let's unify hyps.
    let hpats : List HypPattern ← match hpatstxs? with
         | .none => pure []
         | .some stxs => stxs.toList.mapM HypPattern.parse
    let success ← depthFirstSearchHyps tac hpats ctx
    match success with
    | true => return ()
    | false => throwError m!"matchgoal backtracking search exhaustively failed. Giving up up on '{stx}'."
      -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/master/md/main/tactics.md#tweaking-the-context
    -- then logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal m!"matchgoal failed to find any match"
  | _ => throwUnsupportedSyntax

end MatchGoal
