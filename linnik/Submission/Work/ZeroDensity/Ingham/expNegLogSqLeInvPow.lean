import Mathlib

namespace Work.ZeroDensity.Ingham

/-- If `A ≥ exp 6` and `T ≥ 2` then `exp (-(log (A*T))^2) ≤ 1/T^12`. Indeed
`log (A*T) = log A + log T ≥ 6 + log T`, and `(6+u)^2 - 12u = 36 + u^2 ≥ 0`, so `(log (A*T))^2 ≥ 12 log T = log (T^12)`. -/
theorem expNegLogSqLeInvPow {A T : ℝ} (hA : Real.exp 6 ≤ A) (hT : 2 ≤ T) :
    Real.exp (-(Real.log (A * T)) ^ 2) ≤ 1 / T ^ 12 := by
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos 6) hA
  have hTpos : 0 < T := by linarith
  -- `log T ≥ 0` since `T ≥ 2 ≥ 1`
  have hlogTnn : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
  -- `6 ≤ log A`
  have hlogA : 6 ≤ Real.log A := by
    have h := Real.log_le_log (Real.exp_pos 6) hA
    rwa [Real.log_exp] at h
  -- `log (A*T) = log A + log T ≥ 6 + log T`
  have hlogmul : Real.log (A * T) = Real.log A + Real.log T :=
    Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)
  have hge : 6 + Real.log T ≤ Real.log (A * T) := by rw [hlogmul]; linarith
  -- squaring preserves the inequality since both sides are nonnegative
  have hsq : (6 + Real.log T) ^ 2 ≤ (Real.log (A * T)) ^ 2 := by
    have hba : 0 ≤ Real.log (A * T) - (6 + Real.log T) := sub_nonneg.mpr hge
    have hbpa : 0 ≤ Real.log (A * T) + (6 + Real.log T) := by linarith
    have hprod : 0 ≤ (Real.log (A * T) - (6 + Real.log T)) * (Real.log (A * T) + (6 + Real.log T)) :=
      mul_nonneg hba hbpa
    nlinarith [hprod]
  -- `(6+u)^2 = 36 + 12u + u^2 ≥ 12u`
  have hkey : 12 * Real.log T ≤ (Real.log (A * T)) ^ 2 := by
    nlinarith [hsq, sq_nonneg (Real.log T)]
  -- exponentiate
  have hexpmono : Real.exp (-(Real.log (A * T)) ^ 2) ≤ Real.exp (-(12 * Real.log T)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hrhs : Real.exp (-(12 * Real.log T)) = 1 / T ^ 12 := by
    have hlogT12 : Real.log (T ^ 12) = 12 * Real.log T := by
      rw [Real.log_pow]; norm_num
    rw [← hlogT12, Real.exp_neg, Real.exp_log (pow_pos hTpos 12), one_div]
  calc Real.exp (-(Real.log (A * T)) ^ 2) ≤ Real.exp (-(12 * Real.log T)) := hexpmono
    _ = 1 / T ^ 12 := hrhs

end Work.ZeroDensity.Ingham
