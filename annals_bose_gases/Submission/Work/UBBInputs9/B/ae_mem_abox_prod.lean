import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B

open MeasureTheory

/-- Almost every point of the product of the restricted centred-box measure
`volume ↾ abox 1 ℓ` on `X 1` with the Lebesgue measure on `ℝ³` has its first
coordinate inside `abox 1 ℓ`.

This is the measure-theoretic triviality used to identify `abox 1 ℓ × ℝ³` with
the support of the sliding-window cutoffs: `μ.restrict s` charges only `s`, and
the first marginal of a product measure is `μ` up to a constant. -/
theorem ae_mem_abox_prod (ℓ : ℝ) :
    ∀ᵐ p ∂(((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X 1)).restrict
          (Submission.BoseGases.abox 1 ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      p.1 ∈ Submission.BoseGases.abox 1 ℓ := by
  have hs : MeasurableSet (Submission.BoseGases.abox 1 ℓ) :=
    Submission.BoseGases.abox_measurable 1 ℓ
  -- `volume ↾ abox 1 ℓ` is concentrated on `abox 1 ℓ`
  have h1 : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X 1)).restrict
      (Submission.BoseGases.abox 1 ℓ)), x ∈ Submission.BoseGases.abox 1 ℓ :=
    ae_restrict_mem hs
  -- the first projection of a product measure is quasi-measure-preserving
  exact (Measure.quasiMeasurePreserving_fst
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X 1)).restrict
        (Submission.BoseGases.abox 1 ℓ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3))))).ae h1

end Work.UBBInputs9.B
