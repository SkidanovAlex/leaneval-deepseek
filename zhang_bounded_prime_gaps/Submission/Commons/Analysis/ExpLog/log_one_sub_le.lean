import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.Analysis.ExpLog.log_nat_add_rpow_div_summable_bound

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