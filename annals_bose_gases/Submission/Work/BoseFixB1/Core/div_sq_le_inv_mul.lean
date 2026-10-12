import Mathlib.Data.ENNReal.Inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

theorem div_sq_le_inv_mul {a x y : ENNReal} (ha0 : a ≠ 0) (ha : a ≠ ⊤)
    (h : x ^ 2 ≤ a * y) : (x / a) ^ 2 ≤ a⁻¹ * y := by
  -- (x/a)^2 = (x^2/a)/a, and dividing `x^2 ≤ a*y` by `a` twice gives `x^2/a/a ≤ y/a = a⁻¹*y`.
  have h1 : x ^ 2 / a ≤ y := by
    have h' := ENNReal.div_le_div_right h a
    rwa [mul_comm a y, ENNReal.mul_div_cancel_right ha0 ha] at h'
  have h2 : x ^ 2 / a / a ≤ y / a := ENNReal.div_le_div_right h1 a
  have hp : (x / a) ^ 2 = x ^ 2 / a / a := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_pow]
    ring
  calc (x / a) ^ 2 = x ^ 2 / a / a := hp
    _ ≤ y / a := h2
    _ = a⁻¹ * y := by rw [div_eq_mul_inv, mul_comm]

end Work.BoseFixB1.Core
