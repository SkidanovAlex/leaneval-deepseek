import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

/-
If `∑ lam ≥ 0` and the unordered pair-sum `∑_{i<j} lam i * lam j ≥ 0`, then any convex
combination of the `lam i` with weights `c i ^ 2` (where `∑ c i ^ 2 = 1`) is at most `∑ lam`.

The proof shows first that each individual `lam i` is at most `∑ lam`: from the pair-sum identity
`(∑ lam)^2 = ∑ lam^2 + 2 * pairSum` and `pairSum ≥ 0` we get `∑ lam^2 ≤ (∑ lam)^2`, whence
`lam i ^ 2 ≤ (∑ lam)^2` and (as `∑ lam ≥ 0`) `lam i ≤ ∑ lam`.
-/
open scoped BigOperators in
theorem weighted_sum_le_sum {n : ℕ} {lam c : Fin n → ℝ}
    (h1 : 0 ≤ ∑ i, lam i) (h2 : 0 ≤ ∑ j, ∑ i, if i < j then lam i * lam j else 0)
    (hc : ∑ i, c i ^ 2 = 1) :
    ∑ i, lam i * c i ^ 2 ≤ ∑ i, lam i := by
  set S : ℝ := ∑ i, lam i with hS
  have hSnonneg : 0 ≤ S := h1
  -- pair-sum identity: S^2 = ∑ lam^2 + 2 * pairSum
  have hpair : S ^ 2
      = (∑ i, (lam i) ^ 2) + 2 * (∑ j, ∑ i, if i < j then lam i * lam j else 0) := by
    rw [hS]; exact pairSum_sq lam
  have hsumsq : ∑ i, (lam i) ^ 2 ≤ S ^ 2 := by nlinarith [hpair, h2]
  -- each lam i is at most S
  have hle : ∀ i, lam i ≤ S := by
    intro i
    have hi : (lam i) ^ 2 ≤ S ^ 2 :=
      le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (lam j)) (Finset.mem_univ i)) hsumsq
    by_cases hpos : 0 ≤ lam i
    · have hsq : |lam i| ≤ |S| := sq_le_sq.mp hi
      rwa [abs_of_nonneg hpos, abs_of_nonneg hSnonneg] at hsq
    · have hneg : lam i < 0 := not_le.mp hpos
      linarith
  calc
    ∑ i, lam i * c i ^ 2 ≤ ∑ i, S * c i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg (c i))
    _ = S * ∑ i, c i ^ 2 := by rw [Finset.mul_sum]
    _ = S * 1 := by rw [hc]
    _ = S := by ring
    _ = ∑ i, lam i := hS

end Commons.Analysis.Sigma2