import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

/-! For an eigenvalue tuple with sigma_2 = 1, `(sum lam)^2 ≥ 2` (from the pair-sum identity: `(sum)^2 = sum of squares + 2 * sigma_2 ≥ 2`). In the positive branch this gives `0 < sum lam` and `2 ≤ sum lam ^ 2`, and hence `sum lam ≥ Real.sqrt 2`. -/
open scoped BigOperators in
theorem sigma1_sq_ge_two (lam : Fin 4 → ℝ)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1) :
    2 ≤ (∑ i : Fin 4, lam i) ^ 2 := by
  -- pair-sum identity: (∑ lam) ^ 2 = (∑ lam^2) + 2 * sigma_2
  have hsq := pairSum_sq (a := lam)
  rw [hσ2] at hsq
  -- the sum of squares is nonnegative
  have hnonneg : 0 ≤ ∑ i : Fin 4, (lam i) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (lam i))
  nlinarith

end Commons.Analysis.Sigma2