import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem lintegral_restrict_shift_le {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : MeasurableSet S)
    (a c : EuclideanSpace ℝ (Fin 3)) (h : EuclideanSpace ℝ (Fin 3) → ENNReal) :
    (∫⁻ b, h (b - a + c)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S))
      ≤ ∫⁻ z, h z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- Rewrite the shifted variable as a translation: `b - a + c = b + (c - a)`.
  calc (∫⁻ b, h (b - a + c)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S))
      = ∫⁻ b, h (b + (c - a))
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict S) := by
        simp only [sub_eq_add_neg, add_comm, add_left_comm]
    -- The restricted measure is dominated by the ambient one (`μ.restrict S ≤ μ`).
    _ ≤ ∫⁻ b, h (b + (c - a))
        ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
        MeasureTheory.lintegral_mono' MeasureTheory.Measure.restrict_le_self le_rfl
    -- Lebesgue measure on `ℝ³` is translation invariant.
    _ = ∫⁻ z, h z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
        MeasureTheory.lintegral_add_right_eq_self h (c - a)

end Work.BoseBoxFock.PCFU
