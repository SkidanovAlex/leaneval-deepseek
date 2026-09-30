import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric base case of BW estimate (14) for the value `3263443`:
`(log n)^2/log 2 + 2 log n + log (n+1) + 1 + 1.0826 n ≤ n log 3` for `n = 3263443`.

The proof uses the standard Mathlib decimal bounds `0.6931471803 < log 2`,
`log 2 < 0.6931471808`, `1.0986122885 < log 3`, the monotonicity of `log`, and
`n ≤ 2^22` to obtain `log n ≤ 22 log 2 ≤ 15.25`; the rest is rational arithmetic. -/
theorem est14_regime2_base :
    (Real.log (3263443 : ℝ)) ^ 2 / Real.log 2 + 2 * Real.log (3263443 : ℝ)
      + Real.log (3263444 : ℝ) + 1 + 1.0826 * (3263443 : ℝ) ≤ (3263443 : ℝ) * Real.log 3 := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2low : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
  have h2up : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le
  have h3low : (1.0986 : ℝ) ≤ Real.log 3 := by
    have := Real.log_three_gt_d9; linarith
  have hA0 : 0 ≤ Real.log (3263443 : ℝ) := Real.log_nonneg (by norm_num)
  have hB0 : 0 ≤ Real.log (3263444 : ℝ) := Real.log_nonneg (by norm_num)
  have hA : Real.log (3263443 : ℝ) ≤ (15.25 : ℝ) := by
    have h1 : Real.log (3263443 : ℝ) ≤ Real.log ((2:ℝ)^22) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith [h1, h2up]
  have hB : Real.log (3263444 : ℝ) ≤ (15.25 : ℝ) := by
    have h1 : Real.log (3263444 : ℝ) ≤ Real.log ((2:ℝ)^22) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith [h1, h2up]
  have hA2div : (Real.log (3263443 : ℝ))^2 / Real.log 2 ≤ (336:ℝ) := by
    rw [div_le_iff₀ h2pos]
    have h1 : (Real.log (3263443 : ℝ))^2 ≤ (15.25:ℝ)^2 := by nlinarith [hA, hA0]
    have h2 : (15.25:ℝ)^2 ≤ (336:ℝ) * 0.6931471803 := by norm_num
    have h3 : (336:ℝ) * 0.6931471803 ≤ 336 * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2low (by norm_num)
    linarith
  nlinarith [hA, hB, hA0, hB0, hA2div, h3low, h2pos]

end Work.BW
