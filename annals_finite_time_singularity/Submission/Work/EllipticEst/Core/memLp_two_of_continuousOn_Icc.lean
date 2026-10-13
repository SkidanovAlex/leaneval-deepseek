import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

lemma memLp_two_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  -- On a compact interval the restricted Lebesgue measure is finite and a continuous
  -- function is bounded, so `f` is a.e. bounded on a finite measure space, hence `L²`.
  have hfin : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MeasureTheory.MemLp.of_bound ?_ C ?_
  · exact hf.aestronglyMeasurable measurableSet_Icc
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with x hx
    exact hC x hx

end Work.EllipticEst.Core
