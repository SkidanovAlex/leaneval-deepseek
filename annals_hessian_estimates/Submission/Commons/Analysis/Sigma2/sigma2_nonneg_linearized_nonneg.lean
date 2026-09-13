import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Sigma2.pairSum_sq
import Submission.Commons.Analysis.Sigma2.sum_sq_eq_sigma1_sq_sub_two

namespace Commons.Analysis.Sigma2

/-- **Core inequality.** If a real tuple has nonnegative total sum and its sum of
squares is at most the square of its total sum, then every entry is at most the
total sum.

Indeed `λₖ² ≤ ∑λ² ≤ (∑λ)²` gives `|λₖ| ≤ ∑λ` (using `0 ≤ ∑λ`), hence `λₖ ≤ ∑λ`. -/
theorem le_sum_of_sum_sq_le_sq_sum {n : ℕ} {lam : Fin n → ℝ}
    (h1 : 0 ≤ ∑ i, lam i)
    (h2 : (∑ i, (lam i) ^ 2) ≤ (∑ i, lam i) ^ 2) :
    ∀ i, lam i ≤ ∑ j, lam j := by
  intro k
  have hk : (lam k) ^ 2 ≤ ∑ i : Fin n, (lam i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (lam i)) (Finset.mem_univ k)
  have hk2 : (lam k) ^ 2 ≤ (∑ i : Fin n, lam i) ^ 2 := le_trans hk h2
  have habs : |lam k| ≤ ∑ i : Fin n, lam i := abs_le_of_sq_le_sq hk2 h1
  exact le_trans (le_abs_self (lam k)) habs

open scoped BigOperators in
/-- If the total sum `∑ᵢ λᵢ` is nonnegative and the pair sum `∑_{i<j} λᵢλⱼ` is
nonnegative, then each `λᵢ` is at most the total sum.

This is the linearized form of `σ₂(λ) ≥ 0`: the pair-sum identity
`(∑λ)² = ∑λ² + 2·∑_{i<j}λᵢλⱼ` (`pairSum_sq`) turns the hypothesis on `σ₂` into
`∑λ² ≤ (∑λ)²`, and `le_sum_of_sum_sq_le_sq_sum` finishes. -/
theorem sigma2_nonneg_linearized_nonneg {n : ℕ} {lam : Fin n → ℝ}
    (h1 : 0 ≤ ∑ i, lam i)
    (h2 : 0 ≤ ∑ j, ∑ i, if i < j then lam i * lam j else 0) :
    ∀ i, lam i ≤ ∑ j, lam j := by
  have hpair := pairSum_sq (a := lam)
  have htwo : 0 ≤ 2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then lam i * lam j else 0) :=
    mul_nonneg (by norm_num) h2
  exact le_sum_of_sum_sq_le_sq_sum h1 (by linarith [hpair, htwo])

end Commons.Analysis.Sigma2