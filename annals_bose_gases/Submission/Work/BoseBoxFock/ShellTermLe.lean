import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem ShellTermLe (k : ℕ) (hk : 2 ≤ k) :
    (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) - 1) ^ (-(4 : ℝ)) ≤ 98 * ((k : ℝ) - 1) ^ (-(2 : ℝ)) := by
  -- Write `x = k - 1 ≥ 1`; the claim becomes `(24k²+2) · x⁻⁴ ≤ 98 · x⁻²`,
  -- which after clearing denominators is `24k²+2 ≤ 98x²`, i.e. `2x²(x-1)(37x+13) ≥ 0`.
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx1 : 1 ≤ (k : ℝ) - 1 := by linarith
  have hxpos : 0 < (k : ℝ) - 1 := lt_of_lt_of_le one_pos hx1
  have h4 : ((k : ℝ) - 1) ^ (-(4 : ℝ)) = (((k : ℝ) - 1) ^ 4)⁻¹ := by
    rw [Real.rpow_neg hxpos.le (4 : ℝ)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 4)
  have h2 : ((k : ℝ) - 1) ^ (-(2 : ℝ)) = (((k : ℝ) - 1) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hxpos.le (2 : ℝ)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 2)
  rw [h4, h2]
  simp only [inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ (pow_pos hxpos 4) (pow_pos hxpos 2)]
  nlinarith [sq_nonneg ((k : ℝ) - 1),
    mul_nonneg (mul_nonneg (sq_nonneg ((k : ℝ) - 1)) (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1 - 1))
      (by linarith : (0 : ℝ) ≤ 37 * ((k : ℝ) - 1) + 13)]

end Work.BoseBoxFock
