import Mathlib

namespace Work.FIArea7

theorem tau_pow_succ_eq_sum_divisors (j n : ℕ) :
    ((((n.divisors.card : ℕ) : ℝ))) ^ (j + 1)
      = ∑ d ∈ n.divisors, ((((n.divisors.card : ℕ) : ℝ))) ^ j := by
  have h : ∑ d ∈ n.divisors, ((((n.divisors.card : ℕ) : ℝ))) ^ j
      = ((n.divisors.card : ℕ) : ℝ) * ((((n.divisors.card : ℕ) : ℝ))) ^ j := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h, pow_succ]
  ring

end Work.FIArea7
