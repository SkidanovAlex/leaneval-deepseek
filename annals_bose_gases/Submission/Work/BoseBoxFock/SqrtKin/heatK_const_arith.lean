import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.SqrtKin

/-- Elementary constant identity for the heat-kernel kinetic term:
`(4π)^{-3/2} · (x²/4)^{-2} = 2/(π^{3/2} x⁴)`.
Both sides are `0` at `x = 0` under the convention `1/0 = 0`, so the identity holds
for every real `x`. -/
theorem heatK_const_arith (x : ℝ) :
    (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (1 / (x ^ 2 / 4) ^ 2)
      = 2 / (Real.pi ^ (3 / 2 : ℝ) * x ^ 4) := by
  -- `4^{3/2} = 8`
  have h4 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
    have h' : (4 : ℝ) ^ ((3 : ℝ) / 2) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) := by
      norm_num
    rw [h', ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  -- `(4π)^{-3/2} = (8 π^{3/2})^{-1}`
  have hK : (4 * Real.pi) ^ (-(3 : ℝ) / 2) = (8 * Real.pi ^ ((3 : ℝ) / 2))⁻¹ := by
    have he : -(3 : ℝ) / 2 = -((3 : ℝ) / 2) := by ring
    rw [he, Real.rpow_neg (le_of_lt (by positivity : (0 : ℝ) < 4 * Real.pi))]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt Real.pi_pos), h4]
  -- `1/(x²/4)² = 16 · (x⁴)^{-1}`
  have hS : (1 : ℝ) / (x ^ 2 / 4) ^ 2 = 16 * (x ^ 4)⁻¹ := by
    have h : (x ^ 2 / 4) ^ 2 = x ^ 4 * (16 : ℝ)⁻¹ := by ring
    rw [one_div, h, mul_inv, inv_inv]
    ring
  rw [hK, hS, div_eq_mul_inv, mul_inv]
  ring

end Work.BoseBoxFock.SqrtKin
