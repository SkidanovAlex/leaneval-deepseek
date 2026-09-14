import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open _root_.MeasureTheory Filter

namespace Commons.MeasureTheory.Integral

theorem intervalIntegrable_of_lintegral_ofReal_norm_sq_lt_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hmeas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (h : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioc a b))
      (fun t => ENNReal.ofReal (‖f t‖ ^ 2)) < ⊤) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hL2 : MemLp f 2 (volume.restrict (Set.Ioc a b)) := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    exact ⟨hmeas.norm.pow 2,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => sq_nonneg _)).2 h⟩
  have hL1 : MemLp f 1 (volume.restrict (Set.Ioc a b)) :=
    hL2.mono_exponent (by norm_num)
  exact memLp_one_iff_integrable.mp hL1

end Commons.MeasureTheory.Integral