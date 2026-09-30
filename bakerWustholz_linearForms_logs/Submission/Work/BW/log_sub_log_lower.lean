import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Elementary analytic input for Baker–Wüstholz: for `0 < x ≤ y` and `0 < A`,
`c * (y - x) ≤ A * (log y - log x)` whenever `c * y ≤ A`.
The key inequality is `(y - x) / y ≤ log y - log x`, obtained from
`log t ≤ t - 1` applied to `t = x / y`. -/
theorem log_sub_log_lower {x y c A : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hA : 0 < A)
    (hc : c * y ≤ A) : c * (y - x) ≤ A * (Real.log y - Real.log x) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  -- Key estimate: `(y - x) / y ≤ log y - log x`.
  have hlog : (y - x) / y ≤ Real.log y - Real.log x := by
    have h1 : Real.log (x / y) ≤ x / y - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at h1
    have h3 : (y - x) / y = 1 - x / y := by field_simp
    rw [h3]
    linarith
  have hc' : c ≤ A / y := (le_div_iff₀ hy).mpr hc
  have hyx : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hA0 : 0 ≤ A := le_of_lt hA
  calc c * (y - x) ≤ (A / y) * (y - x) := mul_le_mul_of_nonneg_right hc' hyx
    _ = A * ((y - x) / y) := by ring
    _ ≤ A * (Real.log y - Real.log x) := mul_le_mul_of_nonneg_left hlog hA0

end Work.BW
