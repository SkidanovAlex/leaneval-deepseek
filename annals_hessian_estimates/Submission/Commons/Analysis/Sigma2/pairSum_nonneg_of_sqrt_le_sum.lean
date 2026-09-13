import Mathlib
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology in
theorem pairSum_nonneg_of_sqrt_le_sum {lam : Fin 4 → ℝ}
    (h : Real.sqrt (2 + ∑ i, (lam i) ^ 2) ≤ ∑ i, lam i) :
    0 ≤ ∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0 := by
  -- the pair-sum identity
  have hsq := pairSum_sq (a := lam)
  -- the right-hand side of `h` is nonnegative
  have hT : 0 ≤ ∑ i : Fin 4, lam i := le_trans (Real.sqrt_nonneg _) h
  -- squaring the hypothesis
  have h1 : 2 + ∑ i : Fin 4, (lam i) ^ 2 ≤ (∑ i : Fin 4, lam i) ^ 2 := by
    have hsqrt : (Real.sqrt (2 + ∑ i : Fin 4, (lam i) ^ 2)) ^ 2
        = 2 + ∑ i : Fin 4, (lam i) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hmul : (Real.sqrt (2 + ∑ i : Fin 4, (lam i) ^ 2))
          * (Real.sqrt (2 + ∑ i : Fin 4, (lam i) ^ 2))
        ≤ (∑ i : Fin 4, lam i) * (∑ i : Fin 4, lam i) :=
      mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rw [← pow_two, ← pow_two, hsqrt] at hmul
    exact hmul
  nlinarith [hsq, h1]

end Commons.Analysis.Sigma2
