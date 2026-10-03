import Mathlib
import Submission.Work.FIArea3.JointCount.sweep_defs

namespace Work.FIArea3.JointCount

open MeasureTheory

/-- `hmap z` is a measure preserving real-linear map of `ℂ` when `z ≠ 0`: its determinant is
`1`. -/
theorem volume_image_hmap (z : ℂ) (hz : z ≠ 0) (X : Set ℂ) : MeasureTheory.volume (Work.FIArea3.JointCount.hmap z '' X) = MeasureTheory.volume X := by
  have hne : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have hdet : LinearMap.det (hmap z) = 1 := by
    rw [hmap, LinearMap.det_comp, det_diagScale, det_mulConjZ, one_div, inv_mul_cancel₀ hne]
  rw [MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume (hmap z) X, hdet]
  simp

end Work.FIArea3.JointCount
