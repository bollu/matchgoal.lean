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

/-- pattern of the hypothesis -/
declare_syntax_cat pattern_hyp

/-- pattern of 'term' variable #v -/
declare_syntax_cat pattern_term_var

/-- pattern of hypothesis variable '^H' -/
declare_syntax_cat pattern_hyp_var -- pattern_term_ident maybe?

/-- pattern of expressions -/
declare_syntax_cat pattern_expr

scoped syntax (name := term_var) "#" noWs ident : pattern_term_var
scoped syntax (name := term_var_blank) "#_" : pattern_term_var
scoped syntax (name := hyp_var) "^" noWs ident : pattern_hyp_var
-- scoped syntax (name := hyp_var_blank) "^_" : pattern_term_var


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
  mvars : Std.HashMap PatternName Syntax := {}
  /-- match hypothesis pattern names to their FVarIds in the local context --/
  hyps : Std.HashMap PatternName (PatternHyp × FVarId) := {}
deriving Inhabited

instance : ToMessageData PatternCtx where
  toMessageData pctx := Id.run do
    let mvars := MessageData.ofList <| pctx.mvars.toList.map (fun (k, v) =>  m!"{k} ↦ {v}")
    let hyps := MessageData.ofList <| pctx.hyps.toList.map fun (k, v) => m!"{k} ↦ {(v.snd.name)}"
    m!"PatternCtx({mvars}, {hyps})"


def isSyntaxEq (s : Syntax) (t : Syntax) : Bool :=
  match s, t with
  | Syntax.missing, Syntax.missing => true
  | Syntax.atom  (val := sval) .. , Syntax.atom (val := tval) .. => sval = tval
  | .ident (val := sval) .., .ident (val := tval) .. => sval = tval
  | .node (kind := skind) (args := sargs) .., .node (kind := tkind) (args := targs) .. => Id.run do
      if skind != tkind then return False
      else
        for (sarg, targ) in sargs.zip targs do
          if sarg != targ then return False
        return True
  | _, _ => false

-- Match the syntax 's' against the syntax 't', where 's' is allowed to have patterns.
partial def matcher (pctx : PatternCtx) (s : Syntax) (t : Syntax): TacticM (Option PatternCtx) := do
  trace[matchgoal.debug] "replace s:'{toString s}'"
  match s with -- [Char] --Parser--> Syntax
  | `(pattern_term_var| #$i:ident) | `(term| #$i:ident) => do
     trace[matchgoal.debug] "replace in ident '{i}'"
      match pctx.mvars.find? i.getId with
      | .none => return .some { pctx with mvars := pctx.mvars.insert i.getId t }
      | .some mvarStx =>
        match (← matcher pctx mvarStx t) with
        | .none => return .none
        | .some pctx' => return .some pctx'
  | _ =>
    match s, t with
    | Syntax.missing, Syntax.missing => return .some pctx
    | Syntax.atom  (val := sval) ..  , Syntax.atom (val := tval) .. =>
      return if sval = tval then .some pctx else .none
    | Syntax.ident (val := sval) .., .ident (val := tval) .. =>
      return if sval = tval then .some pctx else .none
    | .node (kind := skind) (args := sargs) .., .node (kind := tkind) (args := targs) .. => do
        if skind != tkind then return .none
        else
          let mut pctx := pctx
          for (sarg, targ) in sargs.zip targs do
            match ← matcher pctx sarg targ with
            | .none => return .none
            | .some pctx' => pctx := pctx'
          return .some pctx
    | _, _ => return .none


  -- | `(pattern_hyp_var| ^$i:ident) | `(term| ^$i:ident) => do
  --     match pctx.hyps.find? i.getId with
  --     | .none => do
  --        trace[matchgoal.debug.matcher] m!"Matchgoal hypothesis variable {i} has not been unified when replacing syntax '{s}'. This is an error."
  --        return .none
  --     | .some (hypPat, _) => do return hypPat.nameStx
  -- | _ =>
  --   match s with
  --   | Syntax.node info kind args => do
  --       let mut args' := #[]
  --       for a in args do
  --          match ← replace pctx a with
  --          | .some a' => args' := args'.push a'
  --          | .none => return .none
  --       return Syntax.node info kind args'
  --   | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s


/-- Instantiate all unification variables in the expression and create a real Lean term.
    Also update the state to recored new unification variables -/
partial def matchAndElab (s : Syntax) (target : Syntax) : StateT PatternCtx TacticM (Option Syntax) := do
  -- trace[matchgoal.debug.matcher] "s:'{toString s}'"
  match s with
  | `(term| $i:ident) | `(pattern_term_var| #$i:ident) =>
    match (← get).mvars.find? i.getId with
    | .some mvarId => (Expr.mvar mvarId).toSyntax
    | .none =>
        let mvarId := (← mkFreshExprMVar
            (type? := .none) (userName := i.getId) (kind := .natural)).mvarId!
        mvarId.assign (← Tactic.elabTerm target (mayPostpone := true) (expectedType? := .none))
        modify (fun ctx => { ctx with mvars := ctx.mvars.insert i.getId mvarId })
        (Expr.mvar mvarId).toSyntax -- TODO: surely there is a helper for this?
  | _ =>
    match s with
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. =>
         if s == target then -- WRONG!
           return s
         else
           trace[matchgoal.debug.matcher] m!"unable to match '{s}' to '{target}'"
           return .none
    | Syntax.node info kind args =>
         match target with
         | Syntax.node info' kind' args' =>
           if kind ≠ kind' || args.size ≠ args'.size then
             trace[matchgoal.debug.matcher] m!"unable to match '{s}' to '{target}'"
             return .none
           else
             for (arg, arg') in args.zip args' do
               xxxadsad
               return Syntax.node info kind (← args.mapM stxholes2mvars) do
         | _ =>
           trace[matchgoal.debug.matcher] m!"unable to match '{s}' to '{target}'"
           return .none

open Lean Elab Macro Tactic in
/--
Replace holes in the Syntax given by `pattern_var` with the values in ctx
TODO: We need to know if we should replace `MVars` or
`Name`s. In the hypothesis manipulation, we should replace MVarIds.
For the final proof production, we should replace `Names` ? -/
-- TODO: replace with 'replacer'?
partial def replace (pctx : PatternCtx) (s : Syntax) : TacticM (Option Syntax) := do
  -- trace[matchgoal.debug] "replace s:'{toString s}'"
  match s with
  | `(pattern_term_var| #$i:ident) | `(term| #$i:ident) => do
     trace[matchgoal.debug] "replace in ident '{i}'"
      match pctx.mvars.find? i.getId with
      | .none => do
          -- TODO: this can be verified statically?
         trace[matchgoal.debug.search] m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         logErrorAt s <|
           MessageData.tagged `Tactic.Matchgoal <|
           m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         return .none
      | .some mvar => return ← (Expr.mvar mvar).toSyntax
  | `(pattern_hyp_var| ^$i:ident) | `(term| ^$i:ident) => do
      match pctx.hyps.find? i.getId with
      | .none => do
         trace[matchgoal.debug.search] m!"Matchgoal hypothesis variable {i} has not been unified when replacing syntax '{s}'. This is an error."
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
    let hpatfilledterm : TSyntax `term ←  monadLift (m := TacticM) <| `([pattern_expr| $hpatfilled])
    let hpatexpr ← Tactic.elabTerm hpatfilledterm (expectedType? := .none) (mayPostpone := .true)
    if ← isDefEq hpatexpr ldeclType -- Makes me sad because TC resolution is sad.
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




structure Depth where
  depth : Nat := 0

def Depth.increment (d: Depth) : Depth where
  depth := d.depth + 1

instance : ToString Depth where
  toString d := String.mk (List.replicate (d.depth*2) ' ')

instance : ToMessageData Depth where
  toMessageData d := toString d


open Lean Core Meta Elab Macro Tactic in
/-- The search state of the backtracking depth first search. -/
def depthFirstSearchHyps
  (depth : Depth)
  (tac : TSyntax `tactic)
  (hyppats : List PatternHyp)
  (pctx : PatternCtx)
  (gpat? : Option (TSyntax `pattern_expr)): TacticM Bool :=  do
  trace[matchgoal.debug.search] m!"==={depth.depth}==="
  trace[matchgoal.debug.search] m!"{depth}STEP: depthFirstSearchHyps {hyppats}"
  match hyppats with
  | [] => do
     let stateBeforeMatcher ← Tactic.saveState
     let mut pctx := pctx
     if let .some gpat := gpat? then
       trace[matchgoal.debug.search] m!"{depth}STEP: matching for goal '{gpat}'"
       -- Do not do this in two steps: do the matching and the elaboration in the same step.
       let (gpatfilled, pctx') ← (stxholes2mvars gpat).run pctx
       let gpatfilled : TSyntax `pattern_expr := ⟨gpatfilled⟩
       pctx := pctx' -- Lean does not have nice syntax to shadow
       let gpatfilledterm ←  monadLift (m := TacticM) <| `([pattern_expr| $gpatfilled])
       trace[matchgoal.debug.search] m!"{depth}STEP: filled goal pattern '{gpatfilledterm}'"
       -- if #k then ... | needs postponing.
       let gpatexpr ← Tactic.elabTerm -- Tactic.elabTermEnsuringType
         (mayPostpone := true)
         gpatfilledterm
         (expectedType? := .none)
         -- (expectedType? := ← inferType (← getMainTarget))
       trace[matchgoal.debug.search] m!"{depth}STEP: isDefEq '{gpatexpr}' '{← getMainTarget}'"
       if not (← isDefEq gpatexpr (← getMainTarget)) then
        trace[matchgoal.debug.search] m!"{depth}  FAILED isDefEq"
        logErrorAt gpat
          <| MessageData.tagged `Tactic.Matchgoal <|
            m! "unable to prove goal pattern {gpatexpr} is definitionally equal to {← getMainTarget}"
        restoreState stateBeforeMatcher
        return False
     trace[matchgoal.debug.search] m!"{depth}STEP: preparing to run tactic '{tac}'."
     trace[matchgoal.debug.search] m!"{depth}replacing into '{tac}' from context {pctx}" -- TODO: make {ctx} nested
     let tac ← match ← replace pctx tac with
        | .some t => pure t
        | .none =>
          restoreState stateBeforeMatcher
          return False
     trace[matchgoal.debug.search] m!"{depth}STEP: running tactic '{tac}'."
     if ← tryTactic (evalTactic tac) then
        trace[matchgoal.debug.search] m!"{depth}SUCCESS running '{tac}'."
        dbg_trace s!"{depth}SUCCESS running '{tac}'."
        return true
     else
        trace[matchgoal.debug.search] m!"FAILURE running '{tac}'."
        dbg_trace s!"{depth}FAILURE running {tac}'."
        restoreState stateBeforeMatcher
        return false
  | hyppat :: hyppats' =>
     let stateBeforeMatcher ← Tactic.saveState
     for hyp in (← getMainDecl).lctx do
       if hyp.isImplementationDetail then continue
       stateBeforeMatcher.restore -- Paranoia. This should ideally not be necessary.
       if let .some ctx'  ← hyppat.matcher pctx hyp then
         if  (← depthFirstSearchHyps depth.increment tac hyppats' ctx' gpat?) then
          return true
     stateBeforeMatcher.restore -- Paranoia. This should ideally not be necessary.
     return False

/-- match goal tactic -/
-- local syntax (name := matchgoal)
scoped syntax (name := matchgoal)
  "matchgoal" ws
  (hyps ws)?
  "⊢" ws (( pattern_expr ws)?) "=>" ws tactic : tactic

-- foobar [[ ident ]] : tactic
open Lean Core Meta Elab Macro Tactic in
@[tactic MatchGoal.matchgoal]
def evalMatchgoal : Tactic := fun stx => -- (stx -> TacticM Unit)
  -- if stx.kind == node and stx[0] == "matchgoal and stx[1] == ....
  match stx with
  | `(tactic| matchgoal
      $[ $[ $hpatstxs? ];* ]?
      ⊢ $[ $gpat?:pattern_expr ]? => $tac:tactic ) => do
    trace[matchgoal.debug] m!"{toString gpat?}"
    let mut pctx : PatternCtx := default
    let hpats : List PatternHyp ← match hpatstxs? with
         | .none => pure []
         | .some stxs => stxs.toList.mapM PatternHyp.parse
    let success ← depthFirstSearchHyps (depth := Depth.mk 0) tac hpats pctx gpat?
    match success with
    | true => return ()
    | false => throwError m!"matchgoal backtracking search exhaustively failed. Giving up up on '{stx}'."
      -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/master/md/main/tactics.md#tweaking-the-context
    -- then logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal m!"matchgoal failed to find any match"
  | _ => throwUnsupportedSyntax

end MatchGoal
