import Mathlib

namespace Work.WilE8.Poly

/-- Substituting the univariate polynomial `P` for the first variable of a bivariate
polynomial with natural coefficients still yields a bivariate polynomial with natural
coefficients.

Concretely: the `ℕ`-valued function `(D, k) ↦ b.eval ![P.eval D, k]` is the evaluation
of some `b' : MvPolynomial (Fin 2) ℕ`.  This is the `ℕ`-coefficient version of the fact
that a polynomial function composed with a polynomial function is again polynomial.

The proof writes `P` as the bivariate polynomial `Q = Polynomial.aeval (X 0) P`
(`X 0` standing for the first coordinate) and sets
`b' = MvPolynomial.aeval (fun i => if i = 0 then Q else X 1) b`, i.e. the substitution
`X 0 ↦ Q`, `X 1 ↦ X 1`; the evaluation identity is then the substitution rule
`MvPolynomial.comp_aeval_apply`. -/
theorem poly_bound (P : Polynomial ℕ) (b : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ, b'.eval ![D, k] = b.eval ![P.eval D, k] := by
  -- `Q` is the bivariate polynomial representing `D ↦ P.eval D` in the first variable.
  let Q : MvPolynomial (Fin 2) ℕ := Polynomial.aeval (MvPolynomial.X 0) P
  -- Substitute `X 0 ↦ Q`, `X 1 ↦ X 1` into `b`.
  refine ⟨MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Q else MvPolynomial.X 1) b, ?_⟩
  intro D k
  -- `Q` evaluates to `P.eval D` at the point `![D, k]`.
  have hQ : (MvPolynomial.aeval ![D, k]) Q = P.eval D := by
    change (MvPolynomial.aeval ![D, k]) (Polynomial.aeval (MvPolynomial.X 0) P) = P.eval D
    rw [← Polynomial.aeval_algHom_apply (MvPolynomial.aeval ![D, k]) (MvPolynomial.X 0) P]
    rw [MvPolynomial.aeval_X]
    simp only [Matrix.cons_val_zero]
    rw [Polynomial.coe_aeval_eq_eval]
  -- The evaluated substitution map is `![P.eval D, k]`.
  have hf : (fun i : Fin 2 => (MvPolynomial.aeval ![D, k])
        ((fun i : Fin 2 => if i = 0 then Q else MvPolynomial.X 1) i)) = ![P.eval D, k] := by
    funext i
    fin_cases i <;> simp [hQ, MvPolynomial.aeval_X]
  -- Unfold the evaluation of the substituted polynomial.
  rw [show MvPolynomial.eval ![D, k]
        (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Q else MvPolynomial.X 1) b)
      = MvPolynomial.aeval ![D, k]
        (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Q else MvPolynomial.X 1) b)
      from rfl]
  rw [MvPolynomial.comp_aeval_apply
        (fun i : Fin 2 => if i = 0 then Q else MvPolynomial.X 1) (MvPolynomial.aeval ![D, k]) b]
  rw [hf, MvPolynomial.aeval_eq_eval]

end Work.WilE8.Poly
