import Mathlib
import Submission.Commons.NumberTheory.Lagarias.finite_check
import Submission.Commons.NumberTheory.Lagarias.exp_mul_log_ge_exp_euler_mascheroni_mul

namespace Commons.NumberTheory.Lagarias

theorem lagarias_inequality_of_robin_upper (h : ∀ n : ℕ, 5041 ≤ n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))) : ∀ n : ℕ, 0 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  intro n hn0
  by_cases hn : n ≤ 5040
  · exact finite_check n hn0 hn
  · have h5041 : 5041 ≤ n := by omega
    have hn3 : 3 ≤ n := by omega
    have hExp := exp_mul_log_ge_exp_euler_mascheroni_mul n hn3
    have hpos : 0 ≤ (harmonic n : ℝ) := Commons.NumberTheory.Harmonic.positive n
    have hRobin := h n h5041
    linarith

end Commons.NumberTheory.Lagarias
