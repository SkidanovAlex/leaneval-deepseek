import Mathlib

namespace Commons.Algebra.BigOperators

theorem prod_sub_prod_eq_sum_split (s : Finset ℕ) (U V : ℕ → ℝ) :
    (∏ p ∈ s, U p) - (∏ p ∈ s, V p)
      = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => q < p), U q) * (U p - V p)
          * (∏ q ∈ s.filter (fun q => p < q), V q) := by
  have h := Finset.prod_add_ordered s V (fun p : ℕ => U p - V p)
  have key : ∀ i : ℕ, V i + (U i - V i) = U i := fun i => by ring
  simp only [key] at h
  have hS :
      (∑ i ∈ s, (U i - V i) * (∏ j ∈ s.filter (fun j => j < i), U j) *
          (∏ j ∈ s.filter (fun j => i < j), V j))
        = ∑ i ∈ s, (∏ j ∈ s.filter (fun j => j < i), U j) * (U i - V i) *
            (∏ j ∈ s.filter (fun j => i < j), V j) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hS] at h
  rw [h]
  ring

end Commons.Algebra.BigOperators
