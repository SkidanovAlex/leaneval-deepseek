import Mathlib

set_option linter.style.haveILetI false

open scoped MeasureTheory

namespace Work.WilE3.Taylor.CaseII

theorem ae_of_ae_linearEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (ν : MeasureTheory.Measure F) [MeasureTheory.Measure.IsAddHaarMeasure ν]
    (T : E ≃ₗ[ℝ] F) {p : F → Prop} (h : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ x ∂μ, p (T x) := by
  -- Push `μ` forward along `T`: this is again an additive Haar measure on `F`.
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (μ.map (T : E → F)) :=
    MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure μ T
  -- A Haar measure on a σ-compact space is σ-finite.
  haveI : MeasureTheory.SigmaFinite (μ.map (T : E → F)) :=
    MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite _
  -- Uniqueness of Haar measure: it is absolutely continuous w.r.t. `ν`.
  have hac : μ.map (T : E → F) ≪ ν :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  -- Hence `p` holds a.e. for the pushforward measure...
  have h' : ∀ᵐ y ∂(μ.map (T : E → F)), p y := hac.ae_le h
  -- ...and unwinding the pushforward gives the claim.
  exact (MeasurableEmbedding.ae_map_iff
    T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding).mp h'

end Work.WilE3.Taylor.CaseII
