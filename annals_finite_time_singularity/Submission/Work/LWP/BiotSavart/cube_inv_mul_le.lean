import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

/-- For `0 ≤ X`, `0 ≤ a` and `X ≤ 2a`, one has `a^{-3}·a ≤ 4·X^{-2}`, i.e.
`1/a² ≤ 4/X²`. -/
theorem cube_inv_mul_le {a X : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (h1 : X ≤ 2 * a) (h2 : a ≤ 3 * X / 2) : (a ^ (3 : ℕ))⁻¹ * a ≤ 4 * (X ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · have hX0 : X = 0 := le_antisymm (by linarith) hX
    subst hX0
    norm_num
  · have hXpos : 0 < X := by nlinarith
    have hL : (a ^ 3)⁻¹ * a = (a ^ 2)⁻¹ := by
      rw [show a ^ 3 = a ^ 2 * a by ring, mul_inv]
      field_simp
    rw [hL]
    calc (a ^ 2)⁻¹ ≤ (X ^ 2 / 4)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)
      _ = 4 * (X ^ 2)⁻¹ := by rw [div_eq_inv_mul, mul_inv, inv_inv]

end Work.LWP.BiotSavart
