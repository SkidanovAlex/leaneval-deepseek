import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluating, at an arbitrary point `x`, the `k`-th iterated `X₀`-partial derivative of a
polynomial that is a univariate polynomial in the variable `X₀` gives the `k`-th iterated
derivative of that univariate polynomial, evaluated at the `0`-th coordinate of `x`.

Route: first prove the chain rule
`MvPolynomial.pderiv 0 (Polynomial.aeval (MvPolynomial.X 0) R) =
  Polynomial.aeval (MvPolynomial.X 0) (Polynomial.derivative R)`
(for instance by `Polynomial.induction_on'` using `MvPolynomial.pderiv_pow`, `pderiv_X_self`,
`pderiv_C_mul`), iterate it `k` times to get
`(MvPolynomial.pderiv 0)^[k] (Polynomial.aeval (MvPolynomial.X 0) R) =
  Polynomial.aeval (MvPolynomial.X 0) ((Polynomial.derivative)^[k] R)`,
and finally evaluate with `Polynomial.aeval_algHom_apply` applied to the algebra hom
`MvPolynomial.eval x` together with `MvPolynomial.eval_X` (`aeval (x 0) S = S.eval (x 0)`). -/
theorem eval_pderiv_iterate_aeval_X {r : ℕ} (x : Fin (r + 1) → ℂ) (k : ℕ) (R : Polynomial ℂ) :
    MvPolynomial.eval x ((MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.X (0 : Fin (r + 1))) R))
      = (Polynomial.derivative^[k] R).eval (x 0) := by
  -- Chain rule: `∂/∂X₀` on `p(X₀)` is `p'(X₀)`, since `∂/∂X₀ (X₀) = 1`.
  have key : ∀ f : Polynomial ℂ,
      MvPolynomial.pderiv (0 : Fin (r + 1))
          (Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) : MvPolynomial (Fin (r+1)) ℂ) f)
        = Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) : MvPolynomial (Fin (r+1)) ℂ)
            (Polynomial.derivative f) := by
    intro f
    have h := Derivation.comp_aeval_eq (R := ℂ) (A := MvPolynomial (Fin (r+1)) ℂ)
        (M := MvPolynomial (Fin (r+1)) ℂ)
        (MvPolynomial.X (0 : Fin (r+1))) (MvPolynomial.pderiv (0 : Fin (r+1))) f
    rw [h]; simp
  -- Iterating the chain rule.
  have hiter : ∀ k : ℕ,
      (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
          (Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) : MvPolynomial (Fin (r+1)) ℂ) R)
        = Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) : MvPolynomial (Fin (r+1)) ℂ)
            ((Polynomial.derivative)^[k] R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, key, Function.iterate_succ_apply']
  rw [hiter k]
  -- Evaluating `X₀` at `x` gives `x 0`, and `aeval` over `ℂ` is `eval`.
  induction (Polynomial.derivative^[k] R) using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial]

end Work.BW
