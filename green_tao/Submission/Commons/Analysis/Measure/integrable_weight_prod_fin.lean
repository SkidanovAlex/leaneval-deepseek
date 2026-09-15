import Mathlib
import Submission.Commons.Analysis.Measure.integrable_fin_prod
import Submission.Commons.Analysis.Integral.integrable_log_add_div_one_add_sq

namespace Commons.Analysis.Measure

open MeasureTheory

/-- The `m`-fold product over the coordinates of the one-dimensional weight
`t ↦ (log(|t|+2)+1)/(1+t²)` is integrable on `ℝ^m`: this is `integrable_fin_prod`
applied to the single-variable integrability lemma. -/
private theorem integrable_weight_fin (m : ℕ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => ∏ j, (Real.log (|x j| + 2) + 1) / (1 + (x j) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) :=
  integrable_fin_prod Commons.Analysis.Integral.integrable_log_add_div_one_add_sq m

theorem integrable_weight_prod_fin (m : ℕ) :
    MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (∏ j, (Real.log (|p.1 j| + 2) + 1) / (1 + (p.1 j) ^ 2))
        * (∏ j, (Real.log (|p.2 j| + 2) + 1) / (1 + (p.2 j) ^ 2)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
  exact (integrable_weight_fin m).mul_prod (integrable_weight_fin m)

end Commons.Analysis.Measure
