import Mathlib.NumberTheory.Harmonic.Bounds

namespace Commons.Analysis.ExpLog

/-- The harmonic sum over `Finset.Icc 1 k` is bounded above by `log k + 1`.

This is the real-valued version of `harmonic_le_one_add_log`, reindexed to the
interval `Icc 1 k` and with reciprocals written as divisions. -/
theorem sum_Icc_one_div_le_log_add_one {k : ℕ} (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Icc 1 k, 1 / (n : ℝ)) ≤ Real.log (k : ℝ) + 1 := by
  have hsum : (∑ n ∈ Finset.Icc 1 k, 1 / (n : ℝ)) = (harmonic k : ℝ) := by
    rw [show (∑ n ∈ Finset.Icc 1 k, 1 / (n : ℝ)) = ∑ n ∈ Finset.Icc 1 k, (n : ℝ)⁻¹ by
      refine Finset.sum_congr rfl ?_
      intro n _
      rw [one_div]]
    rw [harmonic_eq_sum_Icc]
    simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hsum, add_comm]
  exact_mod_cast (harmonic_le_one_add_log k)

end Commons.Analysis.ExpLog