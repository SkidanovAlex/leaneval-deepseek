import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

noncomputable section
open Set Function MeasureTheory Metric Bornology
open scoped Classical ENNReal NNReal

namespace Commons.Analysis.MeasureTheory

/-- A continuous real-valued function on the unit sphere of a finite-dimensional
Euclidean space is integrable with respect to the surface measure
`MeasureTheory.volume.toSphere`. -/
theorem continuous_integrable_sphere
    {n : ℕ} [Nonempty (Fin n)]
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hf : Continuous f) :
    MeasureTheory.Integrable f MeasureTheory.volume.toSphere := by
  let S : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let μ : Measure S := MeasureTheory.volume.toSphere
  change Integrable f μ
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  -- The unit sphere is compact, so the continuous function `f` is bounded.
  have hK : IsCompact (Set.univ : Set S) := isCompact_univ
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ (f '' (Set.univ : Set S) : Set ℝ), ‖x‖ ≤ C := by
    exact IsBounded.exists_norm_le (hK.image_of_continuousOn hf.continuousOn).isBounded
  -- The surface measure of the sphere is finite, hence `f` has finite integral.
  apply HasFiniteIntegral.of_bounded (C := C) (μ := μ)
  filter_upwards with θ
  exact hC (f θ) ⟨θ, trivial, rfl⟩

end Commons.Analysis.MeasureTheory