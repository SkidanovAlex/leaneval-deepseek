import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Filter Function
open scoped Topology Filter ENNReal Interval NNReal

namespace Commons.Analysis.Integral

lemma intervalIntegrable_indicator_mul_continuous {f : ℝ → ℂ} (hf : Continuous f) (c : ℂ)
    {a b p q : ℝ} : IntervalIntegrable
      (fun u : ℝ => (c * Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ)) u) * f u)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a b := by
  let χ : ℝ → ℂ := Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ))
  let g : ℝ → ℂ := fun u => (c * χ u) * f u
  change IntervalIntegrable g volume a b
  have hB : IntervalIntegrable (fun u : ℝ => ‖c‖ * ‖f u‖) volume a b :=
    (hf.intervalIntegrable a b).norm.const_mul ‖c‖
  refine IntervalIntegrable.mono_fun' (g := fun u : ℝ => ‖c‖ * ‖f u‖) hB ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hχ : Measurable χ :=
      Measurable.indicator measurable_const (measurableSet_Ioo : MeasurableSet (Set.Ioo p q))
    exact (hχ.const_mul c).mul hf.measurable
  · refine Eventually.of_forall ?_
    intro u
    have hχu : ‖χ u‖ ≤ 1 := by
      by_cases h : u ∈ Set.Ioo p q <;> simp [χ, h]
    calc
      ‖g u‖ ≤ ‖c * χ u‖ * ‖f u‖ := by
        simp [g, mul_assoc]
      _ ≤ ‖c‖ * ‖f u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg (f u))
        calc
          ‖c * χ u‖ ≤ ‖c‖ * ‖χ u‖ := norm_mul_le c (χ u)
          _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left hχu (norm_nonneg c)
          _ = ‖c‖ := by simp

end Commons.Analysis.Integral