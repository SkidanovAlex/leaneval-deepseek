import Mathlib

set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Transversality.Sard

theorem volume_absolutelyContinuous_hausdorffMeasure (d : ℕ) :
    MeasureTheory.Measure.AbsolutelyContinuous
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
      (MeasureTheory.Measure.hausdorffMeasure (d : ℝ)) := by
  -- On `EuclideanSpace ℝ (Fin d)`, the Euclidean Hausdorff measure `μHE[d]` coincides with
  -- the Lebesgue volume, and by definition it is the `d`-dimensional Hausdorff measure scaled
  -- by a constant factor. Hence volume is a (constant) multiple of `μH[d]`.
  have h := EuclideanSpace.euclideanHausdorffMeasure_eq_volume d
  rw [← h, MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  exact (MeasureTheory.Measure.AbsolutelyContinuous.rfl).smul_left _

end Work.ThomBordism.Transversality.Sard
