import Mathlib.Tactic.Lemma    --For lemma keyword
import Mathlib.Data.Nat.Basic  --For basic theorems about inequalities
import Std.Data.List.Basic     --For list permutations

/-
Inserts a natural number n into a sorted list.
-/
def sInsert (n : Nat) : List Nat -> List Nat
| [] => [n]
| h::t =>
  if n ≤ h then
    n :: h :: t
  else
    h :: sInsert n t

--Insertion sort
def sort : List Nat -> List Nat
| [] => []
| h::t => sInsert h (sort t)

--Predicate for a list being sorted
def sorted : List Nat -> Prop
--An empty list is sorted
| [] => True
--A list containing a single element is sorted
| [_] => True
--A list with more than 2 elements is only sorted if all
--elements are ordered.
| h1 :: h2 :: t => h1 ≤ h2 ∧ sorted (h2 :: t)


/-
If a sorted list is passed to sInsert,
it will return a sorted list after inserting a new elm.
-/
lemma sInsert_sorted (l : List Nat) (n : Nat) :
sorted l -> sorted (sInsert n l) := by
  induction l
  . case nil => simp [sorted]
  . case cons h1 t1 ih =>
    cases t1
    . case nil =>
      by_cases H2 : n ≤ h1
      . case pos => simp [sInsert, H2, sorted]
      . case neg =>
        simp [sInsert, H2, sorted]
        exact Nat.le_of_lt (Nat.lt_of_not_le H2)
    . case cons h2 t =>
      by_cases H2 : n ≤ h1
      . case pos => simp [sInsert, H2, sorted]
      . case neg =>
        by_cases H3 : n ≤ h2
        . case pos =>
          simp [sInsert, H2, sorted, H3]
          intro _
          apply And.intro
          . case left =>
            exact (Nat.le_of_lt (Nat.lt_of_not_le H2))
        . case neg =>
          simp [sInsert, H2, sorted, H3]
          intros H4 H5
          apply And.intro
          . case left => exact H4
          . case right =>
            have ih2 := ih H5
            simp [sInsert, H3] at ih2
            exact ih2

theorem sort_sorted (l : List Nat) :
sorted (sort l) := by
  induction l
  . case nil => simp [sort, sorted]
  . case cons h t ih =>
    simp [sort, sorted]
    exact (sInsert_sorted (sort t) h) ih

/-
My original version of the above proof. I used
a more constructive approach, but it was harder
to read.
-/
-- lemma sInsert_sorted (l : List Nat) (n : Nat) :
-- sorted l -> sorted (sInsert n l) := by
--   induction l
--   . case _ => simp [sorted]
--   . case _ h1 t1 ih =>
--     exact λ H =>
--     match t1 with
--     | [] =>
--       if H2 : n ≤ h1 then by
--         simp [sInsert, H2, sorted]
--       else by
--         simp [sInsert, H2, sorted]
--         exact Nat.le_of_lt (Nat.lt_of_not_le H2)
--     | h2::t =>
--       if H2 : n ≤ h1 then by
--         simp [sInsert, H2, sorted]
--         simp [sorted] at H
--         exact H
--       else
--         if H3 : n ≤ h2 then by
--           simp [sInsert, H2, sorted, H3]
--           apply And.intro
--           . exact (Nat.le_of_lt (Nat.lt_of_not_le H2))
--           . simp [sorted] at H
--             exact H.right
--         else by
--           simp [sInsert, H2, sorted, H3]
--           apply And.intro
--           . exact H.left
--           . simp [sorted] at H
--             have ih2 := ih H.right
--             simp [sInsert, H3] at ih2
--             exact ih2

/-
A list l with n is a permutation of a list
the list with n inserted into it.
-/
lemma sInsert_perm (l : List Nat) (n : Nat) :
List.Perm (n::l) (sInsert n l) := by
  induction l
  . case nil => simp [sInsert]
  . case _ h t ih =>
    simp [sInsert]
    by_cases H : n ≤ h
    . case pos => simp [H]
    . case neg =>
      simp [H];
      apply (List.Perm.trans _ (List.Perm.cons h ih))
      exact List.Perm.swap h n t

/-
Sort returns a permutation of the input list.
-/
theorem sort_perm (l : List Nat) :
List.Perm l (sort l) := by
  induction l
  . case nil => simp [sort]
  . case cons h t ih =>
    simp [sort]
    have H := sInsert_perm (sort t) h
    exact List.Perm.trans (List.Perm.cons h ih) H
