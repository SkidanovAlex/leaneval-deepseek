import Mathlib
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq
import Submission.Work.BourgainPlan.Maximal.ENNReal_sqrt_tsum_tsum_sq_le

open MeasureTheory
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- Discrete Minkowski (triangle) inequality for `ℓ²`-sums of `ℝ≥0∞`-valued kernels, with an
arbitrary index type `ι` for the "column" variable: the `ℓ²` norm over `n` of the `ℓ¹` norm over
`i` is bounded by the `ℓ¹` norm over `i` of the `ℓ²` norms over `n`.

The proof is the same reduction as in `ENNReal_sqrt_tsum_tsum_sq_le`: write the outer `tsum` over
`ℤ` as the supremum of its finite partial sums, apply the finite-index-set Minkowski integral
inequality `Commons.Analysis.MeasureTheory.minkowski_lintegral_sum` with the counting measure on
`ι` (all functions are measurable for the discrete measurable structure on `ι`), and then extend
the inner finite sums over `n` to the full `tsum` by monotonicity. -/
theorem ENNReal_sqrt_tsum_tsum_sq_le_general {ι : Type*} (a : ℤ → ι → ENNReal) :
    (∑' n : ℤ, (∑' i : ι, a n i) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ∑' i : ι, (∑' n : ℤ, (a n i) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hL : (∑' n : ℤ, (∑' i : ι, a n i) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = ⨆ s : Finset ℤ, (∑ n ∈ s, (∑' i : ι, a n i) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact Commons.Analysis.MeasureTheory.iSup_rpow_eq (by norm_num) _
  rw [hL]
  refine iSup_le fun s => ?_
  letI : MeasurableSpace ι := ⊤
  refine le_trans ?_ (ENNReal.tsum_le_tsum fun i =>
    ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum (f := fun n => (a n i) ^ (2 : ℝ)) s) (by norm_num))
  have h := Commons.Analysis.MeasureTheory.minkowski_lintegral_sum (μ := (Measure.count : Measure ι))
    (t := s) (F := fun n (i : ι) => a n i) (p := 2) (by norm_num)
    (fun n => AEMeasurable.of_discrete)
  simpa only [lintegral_count, ENNReal.rpow_eq_pow] using h

end Work.BourgainPlan.Maximal
