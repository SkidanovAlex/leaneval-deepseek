import Mathlib
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs

open MeasureTheory
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- Discrete Minkowski (triangle) inequality for `ℓ²`-sums of `ℝ≥0∞`-valued kernels: the `ℓ²` norm
over `n` of the `ℓ¹`norm over `q` is bounded by the `ℓ¹` norm over `q` of the `ℓ²` norms over `n`. -/
theorem ENNReal_sqrt_tsum_tsum_sq_le (a : ℤ → ℤ → ENNReal) :
    (∑' n : ℤ, (∑' q : ℤ, a n q) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ∑' q : ℤ, (∑' n : ℤ, (a n q) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hL : (∑' n : ℤ, (∑' q : ℤ, a n q) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = ⨆ F : Finset ℤ, (∑ n ∈ F, (∑' q : ℤ, a n q) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact Commons.Analysis.MeasureTheory.iSup_rpow_eq (by norm_num) _
  rw [hL]
  refine iSup_le fun F => ?_
  refine le_trans ?_ (ENNReal.tsum_le_tsum fun q =>
    ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum (f := fun n => (a n q) ^ (2 : ℝ)) F) (by norm_num))
  have h := Commons.Analysis.MeasureTheory.minkowski_lintegral_sum (μ := Measure.count) (t := F)
    (F := fun n (q : ℤ) => a n q) (p := 2) (by norm_num) (fun n => AEMeasurable.of_discrete)
  simpa only [lintegral_count, ENNReal.rpow_eq_pow] using h

end Work.BourgainPlan.Maximal
