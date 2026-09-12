import Mathlib

open Finset
open scoped BigOperators

namespace Commons.Algebra.BigOperators

/-- If three subsets of a finitely-weighted set of total weight `1` carry
weights whose sum exceeds `2`, then all three have a common element.

Proof idea (contrapositive).  With empty triple intersection, every element
lies in at most two of the sets, and since weights are non-negative the total
weight in `A ∪ B ∪ C` is at most `2`.  More precisely, using
inclusion–exclusion `sA + sB = s(A∪B) + s(A∩B)` and the disjointness of
`A ∩ B` and `C`, one gets `sA + sB + sC = s(A∪B) + s((A∩B) ∪ C) ≤ 1 + 1 = 2`. -/
theorem three_sets_intersection_nonempty {α : Type*} [DecidableEq α] (U : Finset α)
    (w : α → ℝ) (hw0 : ∀ x ∈ U, 0 ≤ w x) (hw1 : (∑ x ∈ U, w x) = 1)
    (A B C : Finset α) (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (hsum : 2 < (∑ x ∈ A, w x) + (∑ x ∈ B, w x) + (∑ x ∈ C, w x)) :
    ∃ x : α, x ∈ A ∧ x ∈ B ∧ x ∈ C := by
  classical
  by_contra hn
  push Not at hn
  have hABsub : A ∩ B ⊆ U := by
    intro x hx
    exact hA ((Finset.mem_inter.mp hx).1)
  have hdisc : Disjoint (A ∩ B) C := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    exact hn x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2 hxC
  have hsAB : (∑ x ∈ A, w x) + (∑ x ∈ B, w x)
      = (∑ x ∈ A ∪ B, w x) + (∑ x ∈ A ∩ B, w x) :=
    (Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w)).symm
  have hsC : (∑ x ∈ A ∩ B, w x) + (∑ x ∈ C, w x)
      = ∑ x ∈ (A ∩ B) ∪ C, w x :=
    (Finset.sum_union (s₁ := A ∩ B) (s₂ := C) (f := w) hdisc).symm
  have h1 : (∑ x ∈ A ∪ B, w x) ≤ ∑ x ∈ U, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hA hB) (fun x hx _ => hw0 x hx)
  have h2 : (∑ x ∈ (A ∩ B) ∪ C, w x) ≤ ∑ x ∈ U, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.union_subset hABsub hC) (fun x hx _ => hw0 x hx)
  have hle : (∑ x ∈ A, w x) + (∑ x ∈ B, w x) + (∑ x ∈ C, w x) ≤ 2 := by
    calc
      (∑ x ∈ A, w x) + (∑ x ∈ B, w x) + (∑ x ∈ C, w x)
          = (∑ x ∈ A ∪ B, w x) + (∑ x ∈ A ∩ B, w x) + (∑ x ∈ C, w x) := by rw [hsAB]
      _ = (∑ x ∈ A ∪ B, w x) + ((∑ x ∈ A ∩ B, w x) + (∑ x ∈ C, w x)) := by ring
      _ = (∑ x ∈ A ∪ B, w x) + (∑ x ∈ (A ∩ B) ∪ C, w x) := by rw [hsC]
      _ ≤ (∑ x ∈ U, w x) + (∑ x ∈ U, w x) := add_le_add h1 h2
      _ = 2 := by rw [hw1]; norm_num
  exact (not_lt_of_ge hle) hsum

end Commons.Algebra.BigOperators
