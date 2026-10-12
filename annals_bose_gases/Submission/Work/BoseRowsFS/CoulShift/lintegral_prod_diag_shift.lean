import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.CoulShift

theorem lintegral_prod_diag_shift (a : EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ENNReal) :
    ∫⁻ z, f (z.1 + a, z.2 + a) ∂(MeasureTheory.volume.prod MeasureTheory.volume)
      = ∫⁻ z, f z ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- `z ↦ (z.1 + a, z.2 + a)` is translation by `(a, a)` in the additive group
  -- `EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)`, and `volume.prod volume`
  -- is invariant under translations (it is an additive Haar measure).
  exact MeasureTheory.lintegral_add_right_eq_self f (a, a)

end Work.BoseRowsFS.CoulShift
