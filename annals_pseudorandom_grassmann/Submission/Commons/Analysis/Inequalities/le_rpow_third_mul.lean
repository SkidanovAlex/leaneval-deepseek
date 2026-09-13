import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Inequalities

theorem le_rpow_third_mul {A B K e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (he : 0 ≤ e)
    (h : A ^ 3 ≤ K * e * B ^ 3) : A ≤ (K * e) ^ ((1 : ℝ) / 3) * B := by
  have hKe : 0 ≤ K * e := mul_nonneg hK he
  have hA3 : 0 ≤ A ^ 3 := by positivity
  have hB3 : 0 ≤ B ^ 3 := by positivity
  -- Take the cube root of both sides; x ↦ x^(1/3) is monotone on [0,∞).
  have hstep : (A ^ 3) ^ ((1 : ℝ) / 3) ≤ (K * e * B ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hA3 h (by norm_num)
  have hAroot : (A ^ 3) ^ ((1 : ℝ) / 3) = A := by
    simpa using Real.pow_rpow_inv_natCast hA (by norm_num : (3 : ℕ) ≠ 0)
  have hBroot : (B ^ 3) ^ ((1 : ℝ) / 3) = B := by
    simpa using Real.pow_rpow_inv_natCast hB (by norm_num : (3 : ℕ) ≠ 0)
  have hR : (K * e * B ^ 3) ^ ((1 : ℝ) / 3) = (K * e) ^ ((1 : ℝ) / 3) * B := by
    rw [Real.mul_rpow hKe hB3, hBroot]
  rw [hAroot, hR] at hstep
  exact hstep

end Commons.Analysis.Inequalities