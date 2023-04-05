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
declare_syntax_cat hyps_matcher
declare_syntax_cat unification_var
declare_syntax_cat unification_expr

-- syntax "?" ident : unification_var
-- syntax unification_var : term -- allow unification variables to be used in terms.

elab t:unification_var : term => do
  -- build fake expression here
  sorry


scoped syntax unification_var : unification_expr -- this needs a converter
scoped syntax term : unification_expr
scoped syntax "(" unification_var ":" unification_expr ")" : hyp_matcher
scoped syntax sepBy(hyp_matcher, ";") : hyps_matcher

structure MVar where
  id: MVarId
  
def MVar.toExpr (mvar : MVar) : Expr := Expr.mvar mvar.id
def MVar.ofExpr: Expr → TacticM MVar
| .mvar id => return .mk id
| e => throwError "Internal tactic error: expected mvar, found expression {e}"

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

instance : Alternative MatchGoalM where 
  failure := MatchGoalM.wrap (return [])
  orElse  mas unit2mas := MatchGoalM.wrap do return (← mas) ++ (← unit2mas ())
def runUnificationVar (ctx: PatternCtx) (e: Expr): TSyntax `unification_var → MatchGoalM PatternCtx
| `(unification_var| ?$i:ident) => do 
  match ctx.mvars.find? i.getId with 
  | .none => 
      ctx.restoreState
      let mvar : MVar := ← MVar.ofExpr (← mkFreshExprMVar 
          (type? := .none) (userName := i.getId) (kind := .natural))
      guard (← isDefEq mvar.toExpr e) 
      return (← { ctx with mvars := ctx.mvars.insert i.getId mvar}.saveState)
  | .some mvar => 
      ctx.restoreState
      guard (← isDefEq mvar.toExpr e) 
      ctx.saveState
| _ => MatchGoalM.wrap <| throwUnsupportedSyntax


-- instantiate all unification variables in the expression and create a real Lean term.
-- Also update the state to recored new unification variables
-- TODO: how do I look inside a term and find unification variables?
open Lean Core Meta Elab Macro Tactic in 
def runUnificationExpr (ctx: PatternCtx) (e: Expr) : TSyntax `unification_expr → MatchGoalM PatternCtx
| `(unification_expr| $t:term ) => do
    let te ← Tactic.elabTerm (stx := t) (expectedType? := .none)
    guard (← isDefEq e te) -- mvar ~ te
    return ctx
| `(unification_expr| $var:unification_var ) => runUnificationVar ctx e var 
| _ => MatchGoalM.wrap <| throwUnsupportedSyntax 

open Lean Core Meta Elab Macro Tactic in 
def runHypMatcher (ctx: PatternCtx) : TSyntax `hyp_matcher → MatchGoalM PatternCtx
| `(hyp_matcher| (?$i:ident : $e:unification_expr)) => do 
    ctx.restoreState
    (← getMainDecl).lctx.decls.foldl (init := pure ctx) (fun mctx ldecl? => do 
      ctx.restoreState
      match ldecl? with 
      | .none => return ctx 
      | .some ldecl => Alternative.orElse mctx (fun () => do
        let ldeclType : Expr ← inferType ldecl.toExpr
        let newctx ← runUnificationExpr ctx ldeclType e
        newctx.saveState -- TODO: this should be un-necessary
      ))
| _ => MatchGoalM.wrap <| throwUnsupportedSyntax 
  

  

-- match goal tactic
-- TODO: why does 'local syntax' not work?
-- local syntax (name := matchgoal) 
scoped syntax (name := matchgoal) 
  "matchgoal"
  (hyps_matcher)?
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
        ⊢ $[ $g?:unification_expr ]? => $t ) => do 
        IO.println g?
        return () 
  -- let PatternCtx ←  do 
      -- if let .some g := g? then runGoalMatcher (← getMainDecl).type g -- first bind goal.
      -- if let .some hs := hs? then hs.forM runHypMatcher
  | _ => throwUnsupportedSyntax

end MatchGoal

open MatchGoal in 
example (n : Nat) : n - n = 0 := by 
  matchgoal ⊢ (?x - ?x = 0) => apply (Nat.sub_self ?x)

open MatchGoal in 
example (p: Prop) (prf : p) : p := by 
  matchgoal (?H : ?prf) ⊢ ?prf => exact ?H

open MatchGoal in 
example (x : Int) : (if x > 0 then true else false = true) := by {
  matchgoal ⊢ if ?x then ?y else ?z => cases ?T:?x <;> simp[?T] -- TODO: we want ?T to be gensymd here.
}

def hello := "world"
