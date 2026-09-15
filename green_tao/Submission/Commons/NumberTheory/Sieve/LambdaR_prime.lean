import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Commons.NumberTheory.Sieve

noncomputable def LambdaR (R n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ R),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((R : ℝ) / (d : ℝ))

theorem LambdaR_prime {R n : ℕ} (hn : Nat.Prime n) (hRn : R < n) :
    LambdaR R n = Real.log (R : ℝ) := by
  have h1n : (1 : ℕ) ≠ n := hn.ne_one.symm
  have hnR : ¬ (n ≤ R) := by omega
  rw [LambdaR, Nat.Prime.divisors hn, Finset.sum_filter,
      Finset.sum_pair h1n, if_neg hnR, add_zero]
  simp only [Nat.cast_one, div_one, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    one_mul]
  by_cases hR : 1 ≤ R
  · rw [if_pos hR]
  · rw [if_neg hR]
    have hR0 : R = 0 := by omega
    rw [hR0, Nat.cast_zero, Real.log_zero]

end Commons.NumberTheory.Sieve