import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS_RegExport.RXT.Sys

theorem integrableOn_Ioc_of_abs_bound {S C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) S)))
    (hb : ∀ σ ∈ Set.Ioc (0 : ℝ) S, |f σ| ≤ C) :
    MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) S) MeasureTheory.volume := by
  -- `Ioc 0 S` has finite Lebesgue measure, and `f` is bounded on it by `C`, so
  -- the Bochner integral converges absolutely.
  refine MeasureTheory.IntegrableOn.of_bound ?_ hm C ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hb x hx

end Work.FTS_RegExport.RXT.Sys
