import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace Commons.Analysis.Integral

open MeasureTheory in
theorem aemeasurable_of_nonneg_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p)
    (h : AEMeasurable (fun x => f x ^ p) μ) : AEMeasurable f μ := by
  have hg : Measurable (fun y : ℝ => y ^ (1 / p)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  have hf' : f = fun x => (f x ^ p) ^ (1 / p) := by
    funext x
    rw [← Real.rpow_mul (hf x) p (1 / p), mul_one_div, div_self hp.ne', Real.rpow_one]
  rw [hf']
  exact hg.comp_aemeasurable' h

end Commons.Analysis.Integral