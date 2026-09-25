import Mathlib

namespace Work.Assembly

theorem log_one_sub_ge (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    -(2 * x) ≤ Real.log (1 - x) := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have h2 : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt h1), Real.log_one, zero_sub] at h2
  have h3 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1]
    nlinarith [mul_nonneg (le_of_lt hx0) (show (0:ℝ) ≤ 1 - 2 * x by linarith)]
  have h4 : (1:ℝ) / (1 - x) - 1 = x / (1 - x) := by
    have h : (1 - x) ≠ 0 := ne_of_gt h1
    rw [eq_div_iff h, sub_mul, div_mul_cancel₀ 1 h]
    ring
  linarith

end Work.Assembly
