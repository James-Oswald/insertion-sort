
import Mathlib.Tactic.Lemma    --For lemma keyword
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith  --Forces simp to use linarith
import Mathlib.Logic.Basic
import Mathlib.Data.List.MinMax

theorem mem_implies_erase_smaller (l : List Nat) (x : Nat) :
x ∈ l -> sizeOf (l.erase x) < sizeOf l := by
  intro h
  induction l
  . case nil =>
    simp at h
  . case cons h t ih =>
    simp at h
    cases h
    . case inl H =>
      simp [<-H, List.erase]
    . case inr H =>
      simp [ih H]
      simp [List.erase, H]
      by_cases H2 : (h == x)
      . case pos =>
        simp [H2]
      . case neg =>
        simp [H2]
        simp [Nat.add_lt_add_iff_left, ih H]

def selection_sort (l : List Nat) : List Nat :=
match H : l.minimum with
| none => []
| some m =>
  m :: selection_sort (l.erase m)
decreasing_by
  all_goals simp_wf
  apply mem_implies_erase_smaller
  apply List.minimum_mem
  exact H

#eval selection_sort [3, 2, 1, 4, 5, 6, 7, 8, 9, 10]

--Predicate for a list being sorted
def sorted : List Nat -> Prop
--An empty list is sorted
| [] => True
--A list containing a single element is sorted
| [_] => True
--A list with more than 2 elements is only sorted if all
--elements are ordered.
| h1 :: h2 :: t => h1 ≤ h2 ∧ sorted (h2 :: t)

theorem sort_sorted (l : List Nat) :
sorted (selection_sort l) := by
  induction l
  . case nil =>
    simp [selection_sort, sorted]
  . case cons h t ih =>
    cases H : (h::t).minimum
    . case none =>
      rw [selection_sort, H]
      simp [sorted]
    . case some m =>
      rw [selection_sort, H]
      simp
      by_cases H2: List.minimum (h::t) = h
      . case pos =>
        have T : m = h := sorry --follows from H2
        simp [T, List.erase]
        sorry
      . case neg =>
