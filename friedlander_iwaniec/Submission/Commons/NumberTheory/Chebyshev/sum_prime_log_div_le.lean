import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded

namespace Commons.NumberTheory.Chebyshev

open Finset

/-- The sum over primes `p ≤ N` of `log p / p` is at most `log N + C` uniformly in `N ≥ 1`.

This is the upper-bound half of the first Mertens theorem.  It follows from
Mertens' theorem for the von Mangoldt function
(`Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded`),
since `log p / p = Λ p / p` for prime `p` and the remaining terms of
`∑_{n ≤ N} Λ n / n` are nonnegative. -/
theorem sum_prime_log_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
        ≤ Real.log (N : ℝ) + C := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hb := hbound (N : ℝ) hN1
  rw [Nat.floor_natCast, Real.norm_eq_abs] at hb
  have hvm : (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ))
      ≤ Real.log (N : ℝ) + C₀ := by
    have := (abs_le.mp hb).2
    linarith
  have hprime : (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hprime]
  have hle : (∑ p ∈ (Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / (p : ℝ))
      ≤ ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro n _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  linarith

end Commons.NumberTheory.Chebyshev
