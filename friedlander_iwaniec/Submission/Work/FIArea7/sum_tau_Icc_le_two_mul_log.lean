import Mathlib
import Submission.Work.FIArea7.sum_inv_Icc_le_two_log
import Submission.Work.FIArea7.sum_tau_eq_sum_card_multiples
import Submission.Work.FIArea7.sum_card_multiples_le_mul_harmonic

namespace Work.FIArea7

/-- Sharp summatory-divisor bound: `∑_{n ≤ N} τ(n) ≤ 2 N log(N+2)`.
Proof route: for `n ≥ 1`, `τ(n) = #{d ≤ N : d ∣ n}`, so exchanging the two finite sums
turns the left side into `∑_{d ≤ N} ⌊N/d⌋`; then `⌊N/d⌋ ≤ N/d` over the reals and
`∑_{d ≤ N} 1/d ≤ 2 log(N+2)` (`Work.FIArea7.sum_inv_Icc_le_two_log`). -/
theorem sum_tau_Icc_le_two_mul_log (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ))
      ≤ 2 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
  rw [sum_tau_eq_sum_card_multiples N]
  refine le_trans (sum_card_multiples_le_mul_harmonic N) ?_
  have h := sum_inv_Icc_le_two_log N
  calc (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ))
      ≤ (N : ℝ) * (2 * Real.log ((N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
    _ = 2 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by ring

end Work.FIArea7
