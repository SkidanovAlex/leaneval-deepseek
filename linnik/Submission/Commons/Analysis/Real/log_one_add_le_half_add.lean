import Mathlib
import Submission.Commons.Analysis.Real.log_le_half_sub_inv

namespace Commons.Analysis.Real

/-- For `z ≥ 0`, `log (1+z) ≤ z/2 + z/(2(1+z))`. -/
theorem log_one_add_le_half_add {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1 + z) ≤ z / 2 + z / (2 * (1 + z)) := by
  have hu : 1 ≤ 1 + z := by linarith
  have h := log_le_half_sub_inv hu
  have hzpos : (1 + z) ≠ 0 := by linarith
  have heq : z / 2 + z / (2 * (1 + z)) = ((1 + z) - (1 + z)⁻¹) / 2 := by
    field_simp
    ring
  rwa [heq]

end Commons.Analysis.Real
