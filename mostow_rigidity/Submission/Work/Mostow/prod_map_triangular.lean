import Mathlib

/-!
# The skew product of a measure-preserving map with left translations

If `g : X → X` preserves `μ` and `ν` is a left-invariant measure on a group `K`, then the
"triangular" map `(x, k) ↦ (g x, ψ x * k)` preserves `μ × ν` (for any measurable `ψ`).

This is the measure-theoretic input for pushing forward a Haar measure along the orbit map of
`PO n 1`; see `Submission.Work.Mostow.isMulLeftInvariant_theta`.
-/

namespace Work.Mostow

/-- The skew product `(x, k) ↦ (g x, ψ x * k)` preserves `μ.prod ν` whenever `g` preserves `μ`
and `ν` is left-invariant. -/
theorem prod_map_triangular {X K : Type*} [MeasurableSpace X] [MeasurableSpace K] [Group K]
    [MeasurableMul K] [MeasurableMul₂ K] (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure K)
    [MeasureTheory.Measure.IsMulLeftInvariant ν] [MeasureTheory.SigmaFinite μ]
    [MeasureTheory.SigmaFinite ν] (g : X → X) (hg : Measurable g)
    (hμ : MeasureTheory.Measure.map g μ = μ) (ψ : X → K) (hψ : Measurable ψ) :
    MeasureTheory.Measure.map (fun p : X × K => (g p.1, ψ p.1 * p.2)) (μ.prod ν) = μ.prod ν := by
  have hf : MeasureTheory.MeasurePreserving g μ μ := ⟨hg, hμ⟩
  have hgm : Measurable (Function.uncurry fun a : X => fun k : K => ψ a * k) :=
    (hψ.comp measurable_fst).mul measurable_snd
  have hker : ∀ᵐ a ∂μ, MeasureTheory.Measure.map (fun k : K => ψ a * k) ν = ν :=
    Filter.Eventually.of_forall fun a =>
      (MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := ν) (ψ a))
  exact (hf.skew_product hgm hker).map_eq

end Work.Mostow
