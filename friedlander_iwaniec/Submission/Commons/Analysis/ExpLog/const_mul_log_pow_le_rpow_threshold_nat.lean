import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Commons.Analysis.ExpLog

/-- For any constant `K ≥ 0`, any natural power `n`, and any positive exponent `r`,
`K * (log x)^n ≤ x^r` for all sufficiently large natural `x`.

This is the natural-number threshold version of
`Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold`. -/
theorem const_mul_log_pow_le_rpow_threshold_nat {K : ℝ} (hK : 0 ≤ K) {n : ℕ} {r : ℝ}
    (hr : 0 < r) :
    ∃ X : ℕ, 1 ≤ X ∧ ∀ x : ℕ, X ≤ x → K * (Real.log (x : ℝ)) ^ n ≤ (x : ℝ) ^ r := by
  obtain ⟨X₀, hX₀, h⟩ := const_mul_log_pow_le_rpow_threshold hK hr
  obtain ⟨N, hN⟩ := exists_nat_ge X₀
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := le_trans (le_max_left N 1) hx
  have hxN : X₀ ≤ (x : ℝ) := le_trans hN (by exact_mod_cast hNx)
  exact h x hxN

end Commons.Analysis.ExpLog
