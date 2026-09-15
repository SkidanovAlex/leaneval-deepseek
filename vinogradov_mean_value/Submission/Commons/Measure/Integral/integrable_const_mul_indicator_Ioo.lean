import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.Measure.Integral

theorem integrable_const_mul_indicator_Ioo (c : ℂ) (p q : ℝ) :
    MeasureTheory.Integrable
      (fun u : ℝ => c * Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ)) u)
      MeasureTheory.volume := by
  have hmeas : MeasurableSet (Set.Ioo p q) := measurableSet_Ioo
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ioo p q) MeasureTheory.volume :=
    MeasureTheory.integrableOn_const (measure_Ioo_lt_top.ne)
  have h2 : MeasureTheory.Integrable
      (Set.indicator (Set.Ioo p q) (fun _ : ℝ => (1 : ℂ))) MeasureTheory.volume :=
    h1.integrable_indicator hmeas
  exact h2.const_mul c

end Commons.Measure.Integral