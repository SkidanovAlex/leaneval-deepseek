import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.ExpLog

/-- For `0 ≤ x ≤ 1/2`, `log ((1 - x)⁻¹) ≤ 2 * x`.

Equivalently, `-log (1 - x) ≤ 2x`. Proof: use `log u ≤ u - 1` with
`u = (1 - x)⁻¹` and then `u - 1 = x / (1 - x) ≤ 2x`. -/
theorem log_inv_one_sub_le_two {x : ℝ} (hx0 : 0 ≤ x) (hxle : 2 * x ≤ 1) :
    Real.log ((1 - x)⁻¹) ≤ 2 * x := by
  have h1x : 0 < 1 - x := by linarith
  have hu : 0 < (1 - x)⁻¹ := inv_pos.mpr h1x
  calc
    Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos hu
    _ = x / (1 - x) := by
      field_simp [h1x.ne']
      ring
    _ ≤ 2 * x := by
      rw [div_le_iff₀ h1x]
      calc
        x = x * 1 := by ring
        _ ≤ x * (2 * (1 - x)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hx0
        _ = 2 * x * (1 - x) := by ring

end Commons.Analysis.ExpLog
