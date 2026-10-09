import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.ExpLog

/-- For `0 < x < 1`, `-log (1 - x) ≤ x / (1 - x)`.

Equivalently, with `u = (1 - x)⁻¹`, this is the standard bound `log u ≤ u - 1`. -/
theorem log_one_sub_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  calc
    -Real.log (1 - x) = Real.log ((1 - x)⁻¹) := by rw [← Real.log_inv (1 - x)]
    _ ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
    _ = x / (1 - x) := by
      field_simp [h1x.ne']
      ring

end Commons.Analysis.ExpLog