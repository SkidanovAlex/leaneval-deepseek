import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- An isometry equivalence between finite-dimensional real inner product spaces has the same
dimension on both sides (Mazur–Ulam: an isometric bijection of real normed spaces is affine, so its
linear part is a linear isometry equivalence). -/
lemma finrank_eq_of_isometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ᵢ F) : Module.finrank ℝ E = Module.finrank ℝ F :=
  e.toRealLinearIsometryEquiv.toLinearEquiv.finrank_eq

/-- The Lebesgue measure on a finite-dimensional real inner product space is the Euclidean
Hausdorff measure of the ambient dimension. -/
lemma volume_eq_euclideanHausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    (MeasureTheory.Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) : MeasureTheory.Measure E)
      = MeasureTheory.volume :=
  InnerProductSpace.euclideanHausdorffMeasure_eq_volume

/-- An isometry equivalence between finite-dimensional real inner product spaces preserves the
Lebesgue (Haar) measure, i.e. pushes `volume` forward to `volume`. -/
theorem covolume_isometry_map_volume {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᵢ F) : MeasureTheory.Measure.map e MeasureTheory.volume = MeasureTheory.volume := by
  -- An isometry equivalence forces `finrank ℝ E = finrank ℝ F`, so the same Euclidean Hausdorff
  -- measure `μHE[d]` is the Lebesgue measure on both sides.
  have hfr : Module.finrank ℝ E = Module.finrank ℝ F := finrank_eq_of_isometryEquiv e
  have hmp := e.measurePreserving_euclideanHausdorffMeasure (Module.finrank ℝ E)
  rw [← volume_eq_euclideanHausdorffMeasure (E := E),
      ← volume_eq_euclideanHausdorffMeasure (E := F),
      ← hfr]
  exact hmp.map_eq

end Work.BW
