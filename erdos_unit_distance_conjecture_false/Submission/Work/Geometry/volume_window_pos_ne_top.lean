import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts
import Submission.Work.Geometry.WindowScale
import Submission.Work.Geometry.volume_window_one

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem volume_window_pos_ne_top (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (R : ℝ) (hR : 0 < R) :
    0 < volume (Window K R) ∧ volume (Window K R) ≠ ⊤ := by
  rw [volume_Window_smul R hR, volume_window_one K,
    ← ENNReal.ofReal_mul (pow_pos hR _).le]
  constructor
  · exact ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hR _) (pow_pos Real.pi_pos _))
  · exact ENNReal.ofReal_ne_top

end Work.Geometry
