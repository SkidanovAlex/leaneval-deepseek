import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.Reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

theorem acube_setIntegral_iter_swap (ℓ : ℝ)
    (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hG : MeasureTheory.Integrable (Function.uncurry G)
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, G a b)
      = ∫ b in Submission.BoseGases.acube ℓ, ∫ a in Submission.BoseGases.acube ℓ, G a b := by
  -- The iterated set integrals are Bochner integrals against `volume.restrict (acube ℓ)`.
  -- Integrability of the uncurried kernel against the restricted product measure follows from
  -- `hG` because `(volume.restrict s).prod (volume.restrict s) ≤ volume.prod volume`.
  have hG' : MeasureTheory.Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))) :=
    hG.mono_measure
      (MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
        MeasureTheory.Measure.restrict_le_self)
  exact MeasureTheory.integral_integral_swap hG'

end Work.BoseFixB3.CS.Pieces
