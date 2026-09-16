import Mathlib.Algebra.BigOperators.Intervals

namespace Commons.Combinatorics.Nat

/-- If `f` vanishes on all `j ≥ r`, then the sum of `f` over `Finset.range r` equals
its sum over `Finset.range K` for any `K ≥ r`. -/
theorem sum_range_eq_sum_range_of_eq_zero_of_le {f : ℕ → ℕ} {r K : ℕ} (hrK : r ≤ K) (hz : ∀ j, r ≤ j → f j = 0) : ∑ j ∈ Finset.range r, f j = ∑ j ∈ Finset.range K, f j := by
  rw [← Finset.sum_range_add_sum_Ico f hrK]
  have : ∑ k ∈ Finset.Ico r K, f k = 0 :=
    Finset.sum_eq_zero fun i hi => hz i (Finset.mem_Ico.mp hi).1
  rw [this, add_zero]

end Commons.Combinatorics.Nat