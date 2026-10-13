import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-- For `0 < θ < π/2`, `cos θ / sin θ + sin θ / cos θ + 1 ≤ 3 (sin 2θ)⁻¹`.

Indeed `cos θ / sin θ + sin θ / cos θ = 1/(sin θ cos θ) = 2/sin(2θ)`, so the claim is
equivalent to `1 ≤ 1/sin(2θ)`, i.e. `sin (2θ) ≤ 1`. -/
theorem sinTwoInvBound {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1
      ≤ 3 * (Real.sin (2 * θ))⁻¹ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hcos_pos : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hconv : Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ
      = 2 * (Real.sin (2 * θ))⁻¹ := by
    rw [Real.sin_two_mul]
    field_simp
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [hconv]
  have hs_pos : 0 < Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hs_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ))⁻¹ := by
    have := (inv_le_inv₀ one_pos hs_pos).mpr hs_le
    simpa using this
  linarith

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
