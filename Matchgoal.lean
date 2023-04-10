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

#check Std.HashMap

namespace MatchGoal

open Lean Elab Meta Tactic Term Std RBMap

declare_syntax_cat goal_matcher
declare_syntax_cat hyp_matcher
declare_syntax_cat unification_var
declare_syntax_cat unification_expr

scoped syntax (name := var) "#" noWs ident : unification_var

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

-- 1. var -var2term-> term -term2expr-> expr      --
scoped syntax (name := term2expr) (priority := 0) term : unification_expr
scoped syntax (name := hyp) "(" unification_var ":" unification_expr ")" : hyp_matcher

scoped syntax (name := elabUnificationExpr) "[unification_expr|" unification_expr "]" : term
macro_rules
| `([unification_expr| $e:term]) => return e

syntax hyps := sepBy(hyp_matcher, ";")

structure MVar where
  id: MVarId

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
  -- state of tactic context
  tacticState : Option Tactic.SavedState
 -- map unification variable names to metavars
  mvars : Std.HashMap Name MVar := {}
  -- map hypothesis names to their local declarations
  -- hyps : Std.HashMap Name LocalDecl Compare := {}
  -- if we have goal matcher, map to expression and metavar corresponding to it.
  goalMatcher : Option MVar := .none
deriving Inhabited

def PatternCtx.restoreState (ctx: PatternCtx) : TacticM Unit :=
  match ctx.tacticState with
  | .none => pure ()
  | .some state => MonadBacktrack.restoreState state

def PatternCtx.saveState (ctx: PatternCtx) : TacticM PatternCtx := do
  return { ctx with tacticState := (← MonadBacktrack.saveState) }

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
  trace[matchgoal.unifyVar] "unifyV s:'{toString s}'?"
  match s with
  | `(unification_var| #$i:ident) | `(#$i:ident) => do -- TODO: should I match on 'unification_var' as well?
    trace[matchgoal.unifyVar] "unifyV s:'{toString s}'!"
    match (← get).mvars.find? i.getId with
    | .none =>
        let mvar : MVar := ← MVar.ofExpr (← mkFreshExprMVar
            (type? := .none) (userName := i.getId) (kind := .natural))
        modify (fun ctx => { ctx with mvars := ctx.mvars.insert i.getId mvar })
        mvar.toSyntax
    | .some mvar => mvar.toSyntax
  | _ => throwUnsupportedSyntax


-- instantiate all unification variables in the expression and create a real Lean term.
-- Also update the state to recored new unification variables
-- TODO: how do I look inside a term and find unification variables?
open Lean Core Meta Elab Macro Tactic in
partial def unificationExprFillHoles (s : Syntax) : StateT PatternCtx TacticM Syntax := do
  trace[matchgoal] "s:'{toString s}'"
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
open Lean Elab Macro Tactic in
partial def substitute (ctx: PatternCtx) (s : Syntax) : MatchGoalM Syntax := do
  trace[matchgoal] "substitute s:'{toString s}'"
  match s with
  | `(unification_var| #$i:ident) | `(term| #$i:ident) => do
     -- Here we use the nasty trick of converting an `MVar` into a `Syntax` object.
     match ctx.mvars.find? i.getId with
     | .none => do
        logErrorAt s <| MessageData.tagged `Tactic.Matchgoal <| m!"Matchgoal variable {s} has not been unified. This is an error."
        return s
     | .some mvar =>
        -- TODO: check that mvar has value?
        mvar.toSyntax
  | _ =>
    match s with
    | Syntax.node info kind args => do return Syntax.node info kind (← args.mapM (substitute ctx))
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s




-- match goal tactic
-- TODO: why does 'local syntax' not work?
-- local syntax (name := matchgoal)
scoped syntax (name := matchgoal)
  "matchgoal"
  (hyps)?
  "⊢" (( unification_expr)? <|>  "_") "=>" tactic : tactic

open Lean Meta Elab Tactic in
#check evalSubst
#check Syntax

open Lean Core Meta Elab Macro Tactic in
@[tactic MatchGoal.matchgoal]
def evalMatchgoal : Tactic := fun stx => -- (stx -> TacticM Unit)
  match stx with
  | `(tactic| matchgoal
        $[ $[ $hs? ];* ]?
        ⊢ _ => $t ) => do
        return ()

  | `(tactic| matchgoal
      $[ $[ $hs? ];* ]?
      ⊢ $[ $gpat?:unification_expr ]? => $tac ) => do
        let t ← monadLift (m := TacticM) <| `(unification_var | #v)
        trace[matchgoal] s!"t({toString t})"
        trace[matchgoal] (toString gpat?)
        let tacs ← MatchGoalM.unwrap do
          let mut ctx : PatternCtx := default
          if let .some gpat := gpat? then
             let (gpatmvar, ctx') ← (unificationExprFillHoles gpat).run default
             let gpatmvar : TSyntax `unification_expr := ⟨gpatmvar⟩
             ctx := ctx' -- Lean does not have nice syntax to shadow
             let gpatmvar ←  monadLift (m := TacticM) <| `([unification_expr| $gpatmvar])
             let gpatexpr ← Tactic.elabTerm gpatmvar (expectedType? := .none)
             if not (← isDefEq gpatexpr (← getMainTarget))
             then logErrorAt gpat
              <| MessageData.tagged `Tactic.Matchgoal <| m! "unable to unify goal pattern {gpatexpr} with goal {← getMainTarget}"
          substitute ctx tac
        -- we have many tactics to run
        if tacs.length != 1
        then logErrorAt tac <| MessageData.tagged `Tactic.Matchgoal m!"expected exactly one output state, found {tacs}"
        else
          for t in tacs do
          trace[matchgoal] "running tactic '{t}'."
          match ← tryTactic? (evalTactic t) with
          | .some () => return -- we succeeded with the invocation
          | none => continue -- we failed, so we try the next invocation
        return ()
  | _ => throwUnsupportedSyntax

end MatchGoal
