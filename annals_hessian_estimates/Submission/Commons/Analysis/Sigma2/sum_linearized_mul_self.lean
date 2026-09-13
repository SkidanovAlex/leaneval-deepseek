import Mathlib
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-- The "linearized" form of the symmetric square identity: the sum
`∑ i, (σ₁ - λ_i) λ_i` telescopes to twice the sum over unordered pairs
`∑_{i<j} λ_i λ_j`.  This is the shape in which the identity is used when
differentiating `σ₁` and `σ₂` of an eigenvalue tuple. -/
theorem sum_linearized_mul_self {n : ℕ} (lam : Fin n → ℝ) :
    (∑ i : Fin n, ((∑ t : Fin n, lam t) - lam i) * lam i) =
      2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then lam i * lam j else 0) := by
  have hp := pairSum_sq lam
  have key : (∑ i : Fin n, ((∑ t : Fin n, lam t) - lam i) * lam i) =
      (∑ t : Fin n, lam t) ^ 2 - ∑ i : Fin n, lam i ^ 2 := by
    have h1 : (∑ i : Fin n, ((∑ t : Fin n, lam t) - lam i) * lam i) =
        ∑ i : Fin n, ((∑ t : Fin n, lam t) * lam i - lam i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← pow_two]
  rw [key, hp]
  ring

end Commons.Analysis.Sigma2
