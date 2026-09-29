import Mathlib

namespace Work.TMC14Core

/-- For `q : ℂ[X]`, expanding `q` by the substitution `X ↦ X²` and differentiating twice,
then evaluating at `0`, gives `2 · q'(0)`.

The reason is transparent in coefficients: `coeff (expand ℂ 2 q) n` is `q.coeff (n/2)`
when `2 ∣ n` and `0` otherwise, so the second derivative at `0` picks out
`2 · (expand ℂ 2 q).coeff 2 = 2 · q.coeff 1 = 2 · q'(0)`. -/
theorem deriv2ExpandTwo (q : Polynomial ℂ) :
    (Polynomial.derivative (Polynomial.derivative (Polynomial.expand ℂ 2 q))).eval 0
      = 2 * (Polynomial.derivative q).eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_expand (by norm_num : (0:ℕ) < 2)]
  norm_num
  ring

end Work.TMC14Core
