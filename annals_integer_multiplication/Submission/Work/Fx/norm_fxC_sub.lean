import Mathlib
import Submission.Work.Fx.scaleCommon

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Scaling by `r = ‖c‖`: multiplying by `r` undoes the division by `c`. -/
theorem norm_div_sub_mul {r : ℝ} (hr : 0 < r) {c : ℂ} (hc : ‖c‖ = r) (w x : ℂ) :
    r * ‖w / c - x‖ = ‖w - c * x‖ := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    linarith
  have h1 : w / c - x = (w - c * x) / c := by
    field_simp
  rw [h1, norm_div, hc, mul_div_cancel₀ _ (ne_of_gt hr)]

theorem norm_fxC_sub (p : ℕ) (z : ℤ × ℤ) (x : ℂ) :
    (2 : ℝ) ^ p * ‖HvdH.fxC p z - x‖
      = ‖(z.1 : ℂ) + (z.2 : ℂ) * Complex.I - ((2 : ℝ) ^ p : ℂ) * x‖ := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hnorm : ‖(2 : ℂ) ^ p‖ = (2 : ℝ) ^ p := by
    rw [norm_pow, Complex.norm_ofNat]
  have hcast : (((2 : ℝ) ^ p : ℂ)) = (2 : ℂ) ^ p := by push_cast; ring
  rw [hcast, HvdH.fxC]
  exact norm_div_sub_mul hr hnorm _ _

end Work.Fx
