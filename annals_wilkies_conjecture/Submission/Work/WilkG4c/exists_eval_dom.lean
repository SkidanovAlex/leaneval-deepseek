import Mathlib

namespace Work.WilkG4c

/-- `MvPolynomial.eval` with coefficients in `ℕ` is monotone in the evaluation point: enlarging
every variable value can only increase the value of a polynomial with natural coefficients. -/
theorem eval_le_of_le {σ : Type*} (b : MvPolynomial σ ℕ) {x y : σ → ℕ}
    (h : ∀ i, x i ≤ y i) : MvPolynomial.eval x b ≤ MvPolynomial.eval y b := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_le_sum fun d _ => ?_
  refine Nat.mul_le_mul_left _ ?_
  refine Finset.prod_le_prod fun i _ => ?_
  exact Nat.pow_le_pow_left (h i) _

/-- Substitution commutes with evaluation: evaluating a substitution `bind₁ h φ` at a point `f`
is the same as evaluating `φ` at the pulled-back point `i ↦ eval f (h i)`.  Since `eval f` is
`eval₂Hom (RingHom.id ℕ) f` by definition, this is the universal-property lemma
`MvPolynomial.eval₂Hom_bind₁` for the identity coefficient homomorphism. -/
theorem eval_bind₁ {σ τ : Type*} (h : σ → MvPolynomial τ ℕ) (f : τ → ℕ)
    (φ : MvPolynomial σ ℕ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ h φ)
      = MvPolynomial.eval (fun i => MvPolynomial.eval f (h i)) φ :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) f h φ

/-- **Degree bookkeeping.** A two-variable degree bound `b` evaluated at `![N, r]`, where
`N ≤ D + D1 + c`, is dominated uniformly by a two-variable degree bound `b'` evaluated at
`![D, D1]`. -/
theorem exists_eval_dom (b : MvPolynomial (Fin 2) ℕ) (c r : ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D D1 N : ℕ, N ≤ D + D1 + c →
      MvPolynomial.eval ![N, r] b ≤ MvPolynomial.eval ![D, D1] b' := by
  -- The witness is the substitution `b' = b(X 0 + X 1 + c, r)`, so that evaluating `b'` at
  -- `![D, D1]` gives exactly `eval ![D + D1 + c, r] b`.
  refine ⟨MvPolynomial.bind₁
    ![MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.C c, MvPolynomial.C r] b, ?_⟩
  intro D D1 N hN
  have hfun : (fun i => MvPolynomial.eval ![D, D1]
      (![MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.C c,
          MvPolynomial.C r] i : MvPolynomial (Fin 2) ℕ)) = ![D + D1 + c, r] := by
    funext i
    fin_cases i <;> simp
  rw [eval_bind₁, hfun]
  -- It remains to use monotonicity of `eval` in the first variable, with `N ≤ D + D1 + c`.
  exact eval_le_of_le b (fun i => by fin_cases i <;> simp [hN])

end Work.WilkG4c
