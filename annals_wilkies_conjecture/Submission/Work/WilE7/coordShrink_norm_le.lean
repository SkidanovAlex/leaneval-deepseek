import Mathlib
import Submission.Work.WilE7.fibreAnalyticChartDefs

namespace Work.WilE7

theorem coordShrink_norm_le (m : ℕ) (c : ℝ) (hc : 0 ≤ c) (v : Fin m → ℝ) :
    ‖coordShrink m c v‖ ≤ c / 2 := by
  unfold coordShrink
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro l
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hc,
      abs_of_pos (by positivity : (0:ℝ) < 1 + (v l)^2)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + (v l)^2)]
  have h : 2 * |v l| ≤ 1 + (v l)^2 := by
    nlinarith [sq_nonneg (|v l| - 1), sq_abs (v l)]
  nlinarith [abs_nonneg (v l)]

end Work.WilE7
