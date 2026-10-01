import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.diag_logsum_lower
import Submission.Work.LinnikAreas.Density4.tdQ_ge_logsum

namespace Work.LinnikAreas.Density4

/-- Lower bound for the "saving" sum `tdQ`.

The summand of `tdQ σ A M = Σ_{2 ≤ n ≤ ⌊e^{M-1}⌋} (M - log n - 1) n^{σ-1} e^{-n/A}` is bounded
below on the sub-range `2 ≤ n ≤ ⌊e^{M-2}⌋` by `(6/7) (M - 1 - log n)/n`: indeed `n^{σ-1} ≥ 1/n`
(as `n ≥ 1` and `σ > 0`) and `e^{-n/A} ≥ e^{-e^{-2}} ≥ 6/7` (as `n ≤ e^{M-2}` and `A ≥ e^M`).
The remaining tail `⌊e^{M-2}⌋ < n ≤ ⌊e^{M-1}⌋` contributes nonnegatively since `log n ≤ M-1`.
Finally `Σ_{2 ≤ n ≤ ⌊e^{M-2}⌋} (M - 1 - log n)/n ≥ 0.45 M²` by comparison with the integral
`∫_2^{e^{M-2}} (M-1-log x)/x dx = M(M-2)/2 - (M-1) log 2 + (log 2)²/2`. -/
theorem thetaDiag_Q_lower (M σ A : ℝ) (hM : 15000 ≤ M) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hA : Real.exp M ≤ A) :
    0.34 * M ^ 2 ≤ Work.LinnikAreas.Density4.tdQ σ A M := by
  have hconst : (0.34:ℝ) ≤ (6/7) * 0.45 := by norm_num
  have h1 : (0.34:ℝ) * M^2 ≤ (6/7) * (0.45 * M^2) := by
    calc (0.34:ℝ) * M^2 ≤ ((6/7)*0.45) * M^2 :=
          mul_le_mul_of_nonneg_right hconst (sq_nonneg M)
      _ = (6/7) * (0.45 * M^2) := by ring
  have h2 : (6/7) * (0.45 * M^2)
      ≤ (6/7) * (∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊, (M - 1 - Real.log n)/(n:ℝ)) :=
    mul_le_mul_of_nonneg_left (diag_logsum_lower M hM) (by norm_num)
  have h3 := tdQ_ge_logsum M σ A hM hσ hA
  linarith [h1, h2, h3]

end Work.LinnikAreas.Density4
