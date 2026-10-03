import Mathlib
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp

namespace Work.Pert

/-- **First-order bound for `(exp x - 1)/x` on the disc of radius `1/2`.**

For `x ≠ 0` with `‖x‖ ≤ 1/2`,
`‖(exp x - 1)/x - 1‖ ≤ (29/48) ‖x‖`.

Indeed `(exp x - 1)/x - 1 = (exp x - 1 - x)/x`, so the claim reduces to the sharp
Taylor estimate `‖exp x - 1 - x‖ ≤ (29/48) ‖x‖²` (`norm_exp_sub_one_sub_id_le_sharp`)
divided by `‖x‖`. -/
theorem norm_psi_sub_one_le {x : ℂ} (hx : x ≠ 0) (hx2 : ‖x‖ ≤ 1 / 2) :
    ‖(Complex.exp x - 1) / x - 1‖ ≤ 29 / 48 * ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmain : (Complex.exp x - 1) / x - 1 = (Complex.exp x - 1 - x) / x := by
    rw [div_sub_one hx]
  rw [hmain, Complex.norm_div]
  have hnum := norm_exp_sub_one_sub_id_le_sharp (z := x) hx2
  rw [div_le_iff₀ hxpos]
  calc ‖Complex.exp x - 1 - x‖ ≤ 29 / 48 * ‖x‖ ^ 2 := hnum
    _ = 29 / 48 * ‖x‖ * ‖x‖ := by ring

end Work.Pert
