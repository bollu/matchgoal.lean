import «Matchgoal»
import LSpec

#check Lean.Parser.Tactic.apply
open MatchGoal in
set_option trace.matchgoal true in
def eg1 (n : Nat) : n - n = 0 := by
  matchgoal ⊢ (#x - #x = 0) => apply (Nat.sub_self (#x))

#print eg1
#print eg1.proof_1

open MatchGoal in
example (p: Prop) (prf : p) : p := by
  matchgoal (#H : #prf) ⊢ #prf => xact #H
  sorry

open MatchGoal in
example (x : Int) : (if x > 0 then true else false = true) := by {
  simp
  -- | TODO: need support for 'cases'
  -- matchgoal ⊢ if #x then #y else #z => cases #T:#x <;> simp[#T] -- TODO: we want ?T to be gensymd here.
  sorry
}

def hello := "world"


open LSpec in
def main : IO UInt32 := do
  IO.println s!"Hello, {hello}!"
  lspecIO $
    test "fourIO equals 4" (4 = 4) $
    test "fiveIO equals 5" (5 = 5)