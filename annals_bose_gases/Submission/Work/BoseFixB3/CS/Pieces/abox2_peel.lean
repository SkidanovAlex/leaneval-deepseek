import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.pairFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- **Peeling the two-particle centred box.**  The two-particle box `abox 2 ℓ` is the square
`acube ℓ × acube ℓ` of the one-particle cube, so a kernel depending on the two particle slots
integrates over `abox 2 ℓ` as the iterated integral over `acube ℓ`.

The work is bookkeeping: `Submission.BoseGases.restrict_abox_eq_pi` identifies the restricted
`2`-particle volume with the two-fold product `Measure.pi (fun _ : Fin 2 => ν)`,
`ν = volume.restrict (acube ℓ)`; `measurePreserving_finTwoArrow` transports integrability along
the measurable equivalence `x ↦ (x 0, x 1)` to the product measure `ν.prod ν`; the resulting
statement is exactly the hypothesis of `Work.KinPSuperadd.fubini_abox_two`, which is Fubini
together with the same measure identification. -/
theorem abox2_peel {ℓ : ℝ} {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : MeasureTheory.IntegrableOn (fun u : Submission.BoseGases.X 2 => F (u 0) (u 1))
      (Submission.BoseGases.abox 2 ℓ) MeasureTheory.volume) :
    (∫ u in Submission.BoseGases.abox 2 ℓ, F (u 0) (u 1))
      = ∫ a in Submission.BoseGases.acube ℓ,
          ∫ b in Submission.BoseGases.acube ℓ, F a b := by
  refine Work.KinPSuperadd.fubini_abox_two F ?_
  -- Transport the integrability hypothesis through the measure identification
  -- `volume.restrict (abox 2 ℓ) = Measure.pi (fun _ : Fin 2 => ν)`.
  have hF' : Integrable (fun u : Submission.BoseGases.X 2 => F (u 0) (u 1))
      (Measure.pi (fun _ : Fin 2 =>
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))) := by
    rw [← Submission.BoseGases.restrict_abox_eq_pi 2 ℓ]
    exact hF
  -- ... and then through the measure-preserving equivalence `x ↦ (x 0, x 1)`, which carries
  -- `Measure.pi (fun _ => ν)` to the product measure `ν.prod ν`.
  have hmp := measurePreserving_finTwoArrow
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))
  have hemb : MeasurableEmbedding (MeasurableEquiv.finTwoArrow (α := EuclideanSpace ℝ (Fin 3))) :=
    MeasurableEquiv.measurableEmbedding _
  have hiff := hmp.integrable_comp_emb hemb
    (g := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F p.1 p.2)
  exact hiff.mp hF'

end Work.BoseFixB3.CS.Pieces
