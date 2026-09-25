import Mathlib
import Submission.Commons.NumberTheory.Lagarias.lagarias_inequality_of_robin_upper
import Submission.Commons.NumberTheory.Lagarias.exists_sigma_gt_harmonic_add_exp_mul_log_of_robin_lower

namespace Commons.NumberTheory.Lagarias

/-- The Lemma: given the two halves of Robin's criterion (as hypotheses `h21` and `h22`),
the Riemann hypothesis is equivalent to Lagarias' elementary divisor-sum inequality
`σ(n) ≤ H_n + exp(H_n) log(H_n)` for all `n ≥ 1`.

Forward direction: RH gives Robin's upper bound (`h21`), and
`lagarias_inequality_of_robin_upper` converts Robin's bound into Lagarias' inequality.

Backward direction: if Lagarias' inequality held while RH failed, `h22` would produce some
`n` violating it, a contradiction. -/
theorem riemannHypothesis_iff_lagarias_inequality (h21 : RiemannHypothesis → ∀ n : ℕ, 5041 ≤ n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))) (h22 : ¬ RiemannHypothesis → ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ Filter.Frequently (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≥ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) + C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β) Filter.atTop) : RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  constructor
  · intro hRH
    exact lagarias_inequality_of_robin_upper (h21 hRH)
  · intro hL
    by_contra hnotRH
    obtain ⟨n, hn0, hgt⟩ :=
      exists_sigma_gt_harmonic_add_exp_mul_log_of_robin_lower (h22 hnotRH)
    have hle := hL n hn0
    linarith

end Commons.NumberTheory.Lagarias
