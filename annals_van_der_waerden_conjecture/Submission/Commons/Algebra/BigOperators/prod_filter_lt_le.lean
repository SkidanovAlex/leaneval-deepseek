import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Commons.Algebra.BigOperators

theorem prod_filter_lt_le (s : Finset ℕ) (Y : ℕ) :
    (∏ p ∈ s, p) = (∏ p ∈ s.filter (fun p => p < Y), p) *
      (∏ p ∈ s.filter (fun p => Y ≤ p), p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun p => p < Y) (fun p => p)]
  simp only [not_lt]

end Commons.Algebra.BigOperators