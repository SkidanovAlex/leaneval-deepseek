import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.volume_absolutelyContinuous_hausdorffMeasure

set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Transversality.Sard

open MeasureTheory

/-- A subset of `EuclideanSpace ℝ (Fin d)` whose Hausdorff dimension is strictly less than `d`
has Lebesgue measure zero.  This is the standard "dimension `<` ambient dimension ⇒ measure `0`"
fact: `μH[d] s = 0` whenever `dimH s < d`, and Lebesgue volume on `ℝ^d` is a constant multiple of
`μH[d]`. -/
theorem volume_eq_zero_of_dimH_lt {d : ℕ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (h : dimH s < d) : MeasureTheory.volume s = 0 := by
  have h' : dimH s < ((d : NNReal) : ENNReal) := by simpa using h
  have hac : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) ≪
      MeasureTheory.Measure.hausdorffMeasure ((d : NNReal) : ℝ) := by
    simpa using volume_absolutelyContinuous_hausdorffMeasure d
  exact measure_zero_of_dimH_lt hac h'

end Work.ThomBordism.Transversality.Sard
