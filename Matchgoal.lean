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

declare_syntax_cat pattern_hyp
declare_syntax_cat pattern_term_var
declare_syntax_cat pattern_hyp_var
declare_syntax_cat pattern_expr

scoped syntax (name := term_var) "#" noWs ident : pattern_term_var
scoped syntax (name := hyp_var) "^" noWs ident : pattern_hyp_var


/- Names that are created from `#<name>` syntax. -/
@[reducible]
def PatternName := Name

open Lean Elab in

/-- every unification variable is a term. -/
scoped elab (name := termvar2term) t:pattern_term_var : term => do
  let s : Syntax ←
    match t with
    | `(pattern_term_var| #$i:ident) => pure i
    | _ => throwUnsupportedSyntax
  elabTerm s (expectedType? := .none)


/-- every hypothesis variable is an ident. -/
scoped elab (name := hypvar2ident) t:pattern_hyp_var : term => do
  let s : Syntax ←
    match t with
    | `(pattern_hyp_var| ^$i:ident) => pure i
    | _ => throwUnsupportedSyntax
  elabTerm s (expectedType? := .none)


/--  var -var2term-> term -term2expr-> expr -/
scoped syntax (name := term2expr) (priority := 0)
  term : pattern_expr

scoped syntax (name := hyp)
  "(" pattern_hyp_var ws ":" ws pattern_expr ")" : pattern_hyp

scoped syntax (name := elabUnificationExpr)
  "[pattern_expr|" pattern_expr "]" : term
macro_rules
| `([pattern_expr| $e:term]) => return e

syntax hyps := sepBy(pattern_hyp, "; ")


structure PatternHyp where
  /-- for position information. TODO: pull position out of the raw Tsyntax? -/
  nameStx : Syntax.Ident
  rhs : TSyntax `pattern_expr

-- @[computed_field] TODO: figure out how to use computed fields.
def PatternHyp.name (p : PatternHyp) : Name  := p.nameStx.getId

instance : ToMessageData PatternHyp where
  toMessageData h := m!"{h.nameStx} : {h.rhs}"
def PatternHyp.parse : TSyntax `pattern_hyp →  TacticM PatternHyp
| `(pattern_hyp| (^$i: ident : $e:pattern_expr)) =>
   return { nameStx := i, rhs := e }
| stx => do
  logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal <| m! "unknown hypothesis pattern '{stx}'"
  throwUnsupportedSyntax

structure PatternCtx where
  mvars : Std.HashMap PatternName MVarId := {}
  /-- match hypothesis pattern names to their FVarIds in the local context --/
  hyps : Std.HashMap PatternName (PatternHyp × FVarId) := {}
deriving Inhabited

instance : ToMessageData PatternCtx where
  toMessageData pctx := Id.run do
    let mvars := MessageData.ofList <| pctx.mvars.toList.map (fun (k, v) =>  m!"{k} ↦ {v}")
    let hyps := MessageData.ofList <| pctx.hyps.toList.map fun (k, v) => m!"{k} ↦ {(v.snd.name)}"
    m!"PatternCtx({mvars}, {hyps})"

/-- Instantiate the variable as a Mvar. -/
def pattermTermVar2Mvar (s : TSyntax `pattern_term_var) :
  StateT PatternCtx TacticM (Syntax.Term) := do
  trace[matchgoal.debug.matcher] m!"patternV s:'{toString s}'?"
  match s with
  | `(pattern_term_var| #$i:ident) | `(#$i:ident) => do
    match (← get).mvars.find? i.getId with
    | .some mvarId => (Expr.mvar mvarId).toSyntax
    | .none =>
        let mvarId := (← mkFreshExprMVar
            (type? := .none) (userName := i.getId) (kind := .natural)).mvarId!
        modify (fun ctx => { ctx with mvars := ctx.mvars.insert i.getId mvarId })
        (Expr.mvar mvarId).toSyntax -- TODO: surely there is a helper for this?
  | _ => throwUnsupportedSyntax


open Lean Core Meta Elab Macro Tactic in
/-- Instantiate all unification variables in the expression and create a real Lean term.
    Also update the state to recored new unification variables -/
partial def stxholes2mvars (s : Syntax) : StateT PatternCtx TacticM Syntax := do
  trace[matchgoal.debug.matcher] "s:'{toString s}'"
  match s with
  | `(term| $var:pattern_term_var) => pattermTermVar2Mvar var
  | _ =>
    match s with
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s
    | Syntax.node info kind args =>
         return Syntax.node info kind (← args.mapM stxholes2mvars)

open Lean Elab Macro Tactic in
/--
Replace holes in the Syntax given by `pattern_var` with the values in ctx
TODO: We need to know if we should replace `MVars` or
`Name`s. In the hypothesis manipulation, we should replace MVarIds.
For the final proof production, we should replace `Names` ? -/
-- TODO: replace with 'replacer'?
partial def replace (pctx : PatternCtx) (s : Syntax) : TacticM (Option Syntax) := do
  trace[matchgoal.debug] "replace s:'{toString s}'"
  match s with
  | `(pattern_term_var| #$i:ident) | `(term| #$i:ident) => do
     trace[matchgoal.debug] "replace in ident '{i}'"
      match pctx.mvars.find? i.getId with
      | .none => do
         trace[matchgoal.debug.matcher] m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         logErrorAt s <|
           MessageData.tagged `Tactic.Matchgoal <|
           m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         return .none
      | .some mvar => return ← (Expr.mvar mvar).toSyntax
  | `(pattern_hyp_var| ^$i:ident) | `(term| ^$i:ident) => do
      match pctx.hyps.find? i.getId with
      | .none => do
         trace[matchgoal.debug.matcher] m!"Matchgoal hypothesis variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         return .none
      | .some (hypPat, _) => do return hypPat.nameStx
  | _ =>
    match s with
    | Syntax.node info kind args => do
        let mut args' := #[]
        for a in args do
           match ← replace pctx a with
           | .some a' => args' := args'.push a'
           | .none => return .none
        return Syntax.node info kind args'
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s



open Lean Core Elab Meta Macro Tactic in
def PatternHyp.matcher (pctx: PatternCtx)
  (hpat : PatternHyp)
  (ldecl: LocalDecl) : TacticM (Option PatternCtx) := do
    let ldeclType : Expr ← inferType ldecl.toExpr
    trace[matchgoal.debug.matcher] "PatternHyp.matcher {pctx} : {hpat} =?= {ldeclType}"
    -- | TODO: refactor code duplication
    let (hpatfilled, pctx) ← (stxholes2mvars hpat.rhs.raw).run pctx
    let hpatfilled : TSyntax `pattern_expr := ⟨hpatfilled⟩
    let hpatfilledterm ←  monadLift (m := TacticM) <| `([pattern_expr| $hpatfilled])
    let hpatexpr ← Tactic.elabTerm hpatfilledterm (expectedType? := .none)
    if ← isDefEq hpatexpr ldeclType
    then do
        -- TODO: ask Henrik if this is the optimal way.
        -- Convert the given goal `Ctx |- target` into `Ctx |- type -> target`.
        -- let newgoal ← (← getMainGoal).assert hpat.name ldeclType hpatexpr
        let newgoal ← (← getMainGoal).assert hpat.name ldeclType ldecl.toExpr
        -- `intros` the arrow.
        let (hypFVar, newgoal) ← newgoal.intro1P
        replaceMainGoal [newgoal]
        pure (.some { pctx with hyps := pctx.hyps.insert hpat.name (hpat, hypFVar) })
    else
      trace[matchgoal.debug.matcher] "FAILURE: PatternHyp.matcher {pctx} : {hpat} =!= {ldeclType}"
      return .none


/-- match goal tactic -/
-- TODO: why does 'local syntax' not work?
-- local syntax (name := matchgoal)
scoped syntax (name := matchgoal)
  "matchgoal" ws
  (hyps ws)?
  "⊢" ws (( pattern_expr ws)?) "=>" ws tactic : tactic


open Lean Core Meta Elab Macro Tactic in
/-- The search state of the backtracking depth first search. -/
def depthFirstSearchHyps
  (tac : TSyntax `tactic)
  (hyppats : List PatternHyp)
  (pctx : PatternCtx)
  (gpat? : Option (TSyntax `pattern_expr)): TacticM Bool :=  do
  trace[matchgoal.debug.search] m!"STEP: depthFirstSearchHyps {hyppats}"
  match hyppats with
  | [] => do
     let mut pctx := pctx
     let stateBeforeMatcher ← Tactic.saveState
     if let .some gpat := gpat? then
       let (gpatfilled, pctx') ← (stxholes2mvars gpat).run pctx
       let gpatfilled : TSyntax `pattern_expr := ⟨gpatfilled⟩
       pctx := pctx' -- Lean does not have nice syntax to shadow
       let gpatfilledterm ←  monadLift (m := TacticM) <| `([pattern_expr| $gpatfilled])
       let gpatexpr ← Tactic.elabTerm gpatfilledterm (expectedType? := .none)
       if not (← isDefEq gpatexpr (← getMainTarget)) then
        logErrorAt gpat
          <| MessageData.tagged `Tactic.Matchgoal <| m! "unable to matcher goal pattern {gpatexpr} with goal {← getMainTarget}"
        restoreState stateBeforeMatcher
      trace[matchgoal.debug.search] m!"STEP: preparing to run tactic '{tac}'."
      trace[matchgoal.debug.search] m!"replacing into '{tac}' from context {pctx}" -- TODO: make {ctx} nested
      let tac ← match ← replace pctx tac with
        | .some t => pure t
        | .none =>
          restoreState stateBeforeMatcher
          return False
      trace[matchgoal.debug] m!"========================="
      trace[matchgoal.debug.search] m!"STEP: running tactic '{tac}'."
      if ← tryTactic (evalTactic tac) then
        trace[matchgoal.debug.search] m!"SUCCESS running '{tac}'."
        dbg_trace s!"SUCCESS running '{tac}'."
        return true
      else
        trace[matchgoal.debug.search] m!"FAILURE running '{tac}'."
        dbg_trace s!"FAILURE running {tac}'."
        restoreState stateBeforeMatcher
        return false
  | hyppat :: hyppats' =>
     let stateBeforeMatcher ← Tactic.saveState
     for hyp in (← getMainDecl).lctx do
       if hyp.isImplementationDetail then continue
       stateBeforeMatcher.restore -- bring back state before matchering.
       if let .some ctx'  ← hyppat.matcher pctx hyp then
         if  (← depthFirstSearchHyps tac hyppats' ctx' gpat?) then
          return true
     stateBeforeMatcher.restore
     return False

open Lean Core Meta Elab Macro Tactic in
@[tactic MatchGoal.matchgoal]
def evalMatchgoal : Tactic := fun stx => -- (stx -> TacticM Unit)
  match stx with
  | `(tactic| matchgoal
      $[ $[ $hpatstxs? ];* ]?
      ⊢ $[ $gpat?:pattern_expr ]? => $tac ) => do
    trace[matchgoal.debug] m!"{toString gpat?}"
    let mut pctx : PatternCtx := default
    let hpats : List PatternHyp ← match hpatstxs? with
         | .none => pure []
         | .some stxs => stxs.toList.mapM PatternHyp.parse
    let success ← depthFirstSearchHyps tac hpats pctx gpat?
    match success with
    | true => return ()
    | false => throwError m!"matchgoal backtracking search exhaustively failed. Giving up up on '{stx}'."
      -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/master/md/main/tactics.md#tweaking-the-context
    -- then logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal m!"matchgoal failed to find any match"
  | _ => throwUnsupportedSyntax

end MatchGoal
