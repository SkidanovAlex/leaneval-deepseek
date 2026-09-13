import Mathlib
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology in
theorem pairSum_nonneg_of_sqrt_le_sum_fin {n : ℕ} {lam : Fin n → ℝ}
    (h : Real.sqrt (2 + ∑ i, (lam i) ^ 2) ≤ ∑ i, lam i) :
    0 ≤ ∑ j : Fin n, ∑ i : Fin n, if i < j then lam i * lam j else 0 := by
  -- the pair-sum identity: (∑ lam)^2 = ∑ lam^2 + 2 * (pair sum)
  have hsq := pairSum_sq (a := lam)
  -- squaring the hypothesis
  have h1 : 2 + ∑ i : Fin n, (lam i) ^ 2 ≤ (∑ i : Fin n, lam i) ^ 2 := by
    have hsqrt : (Real.sqrt (2 + ∑ i : Fin n, (lam i) ^ 2)) ^ 2
        = 2 + ∑ i : Fin n, (lam i) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hmul : (Real.sqrt (2 + ∑ i : Fin n, (lam i) ^ 2))
          * (Real.sqrt (2 + ∑ i : Fin n, (lam i) ^ 2))
        ≤ (∑ i : Fin n, lam i) * (∑ i : Fin n, lam i) :=
      mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rw [← pow_two, ← pow_two, hsqrt] at hmul
    exact hmul
  nlinarith [hsq, h1]

end Commons.Analysis.Sigma2
