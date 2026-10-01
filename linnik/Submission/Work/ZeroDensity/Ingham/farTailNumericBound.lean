import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Elementary numeric bound: for `1 ≤ Y ≤ T²` and `T ≥ 2`,
`2 (Y+1) e · (1/T^12) ≤ 1/20`. Since `Y+1 ≤ 2T²`, the left side is at most
`4 e / T^10 ≤ 12/2^10 < 1/20`. -/
theorem farTailNumericBound {Y T : ℝ} (hY : 1 ≤ Y) (hT : 2 ≤ T) (hYT : Y ≤ T ^ 2) :
    2 * (Y + 1) * Real.exp 1 * (1 / T ^ 12) ≤ 1 / 20 := by
  have hTpos : (0:ℝ) < T := by linarith
  have hT2pos : (0:ℝ) < T ^ 2 := by positivity
  have hT12pos : (0:ℝ) < T ^ 12 := by positivity
  have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hepos : (0:ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
  have hY1 : Y + 1 ≤ 2 * T ^ 2 := by linarith
  have hbound : 2 * (Y + 1) * Real.exp 1 ≤ 12 * T ^ 2 := by
    have h1 : 2 * (Y + 1) ≤ 4 * T ^ 2 := by linarith
    have h2 : 2 * (Y + 1) * Real.exp 1 ≤ 4 * T ^ 2 * 3 :=
      mul_le_mul h1 he hepos (by positivity)
    linarith
  have hT10 : (1024:ℝ) ≤ T ^ 10 := by
    have h : (2:ℝ) ^ 10 ≤ T ^ 10 := pow_le_pow_left₀ (by norm_num) hT 10
    norm_num at h
    exact h
  have hT12big : 240 * T ^ 2 ≤ T ^ 12 := by
    have h240 : (240:ℝ) ≤ T ^ 10 := by linarith
    have := mul_le_mul_of_nonneg_right h240 (le_of_lt hT2pos)
    calc (240:ℝ) * T ^ 2 ≤ T ^ 10 * T ^ 2 := this
      _ = T ^ 12 := by ring
  rw [show 2 * (Y + 1) * Real.exp 1 * (1 / T ^ 12) = 2 * (Y + 1) * Real.exp 1 / T ^ 12 by ring]
  rw [div_le_iff₀ hT12pos]
  nlinarith [hbound, hT12big]

end Work.ZeroDensity.Ingham
