import Mathlib

namespace Work.ZeroDensity.Jutila

/-- For `1 ≤ z`, the square of `Real.log z` is at most `4 * z`; this is the sharp
form of the elementary bound `(log x)^2 ≤ 4x`, obtained from
`Real.log x ≤ 2 * sqrt x`. -/
theorem log_sq_le_four_mul_self (z : ℕ) (hz : 1 ≤ z) :
    (Real.log (z : ℝ)) ^ 2 ≤ 4 * (z : ℝ) := by
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast Nat.zero_le z
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlog_nonneg : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg hz1
  -- `log x ≤ x^(1/2) / (1/2) = 2 * sqrt x`
  have hbound : Real.log (z : ℝ) ≤ 2 * Real.sqrt (z : ℝ) := by
    have h := Real.log_le_rpow_div (x := (z : ℝ)) (ε := (1 : ℝ) / 2) hz0 (by norm_num)
    rw [Real.sqrt_eq_rpow]
    have hdiv : (z : ℝ) ^ (1 / 2) / (1 / 2) = 2 * (z : ℝ) ^ (1 / 2) := by norm_num
    linarith [h, hdiv.le, hdiv.ge]
  have hsq := pow_le_pow_left₀ hlog_nonneg hbound 2
  have hsq2 : (2 * Real.sqrt (z : ℝ)) ^ 2 = 4 * (z : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hz0]; norm_num
  linarith [hsq, hsq2.symm.le]

theorem LogSqLeFourN (z N : ℕ) (hz : 1 ≤ z) (hzN : z ≤ N) :
    (Real.log (z : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by
  have hzN' : (z : ℝ) ≤ (N : ℝ) := by exact_mod_cast hzN
  linarith [log_sq_le_four_mul_self z hz, hzN']

end Work.ZeroDensity.Jutila
