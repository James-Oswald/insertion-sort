
import Mathlib.Tactic.Lemma    --For lemma keyword
import Mathlib.Tactic.Basic    --For simp, linarith, etc.


theorem mem_implies_erase_smaller (l : List Nat) (x : Nat) :
x ∈ l -> sizeOf (l.erase x) < sizeOf l := by
  intro h
  induction l
  . case nil =>
    simp at h
  . case cons h t ih =>
    simp at h
    cases h
    . case inl h =>
      simp [<-h, List.erase]
