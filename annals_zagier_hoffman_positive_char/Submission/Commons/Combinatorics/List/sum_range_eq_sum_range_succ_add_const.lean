import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Commons.Combinatorics.List

theorem sum_range_eq_sum_range_succ_add_const {q K r : ℕ} (f : ℕ → ℕ) (hKr : K + 1 ≤ r) (hdiv : ∀ j, K < j → j < r → f j = q - 1) : ∑ j ∈ Finset.range r, f j = (∑ j ∈ Finset.range (K + 1), f j) + (r - (K + 1)) * (q - 1) := by
  -- split the range `r = (K+1) + (r-(K+1))`
  have hsplit := Finset.sum_range_add (f := f) (n := K + 1) (m := r - (K + 1))
  rw [Nat.add_sub_cancel' hKr] at hsplit
  rw [hsplit]
  -- the tail is a constant sum
  have hsum : ∑ x ∈ Finset.range (r - (K + 1)), f ((K + 1) + x) = (r - (K + 1)) * (q - 1) := by
    have h1 : ∀ x ∈ Finset.range (r - (K + 1)), f ((K + 1) + x) = q - 1 := by
      intro x hx
      rw [Finset.mem_range] at hx
      exact hdiv _ (by omega) (by omega)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range]
    simp
  rw [hsum]

end Commons.Combinatorics.List