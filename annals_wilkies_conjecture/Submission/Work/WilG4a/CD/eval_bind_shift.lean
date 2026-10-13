import Mathlib

namespace Work.WilG4a.CD

/-- Evaluating a polynomial that has been substituted through `MvPolynomial.aeval`:
`eval v (aeval f p) = eval (fun i => eval v (f i)) p`. -/
theorem eval_aeval_eq {σ τ R : Type*} [CommSemiring R] (v : τ → R)
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    MvPolynomial.eval v (MvPolynomial.aeval f p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval v (f i)) p := by
  rw [MvPolynomial.aeval_eq_bind₁]
  exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id R) v f p

theorem eval_bind_shift (b : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ,
      MvPolynomial.eval ![D, 1] b' = MvPolynomial.eval ![D + K, 1] b := by
  refine ⟨MvPolynomial.aeval
    (![MvPolynomial.X 0 + MvPolynomial.C K, 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) b, ?_⟩
  intro D
  rw [eval_aeval_eq (![D, 1] : Fin 2 → ℕ)
    (![MvPolynomial.X 0 + MvPolynomial.C K, 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) b]
  have hfun : (fun i : Fin 2 => MvPolynomial.eval (![D, 1] : Fin 2 → ℕ)
        ((![MvPolynomial.X 0 + MvPolynomial.C K, 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) i))
      = (![D + K, 1] : Fin 2 → ℕ) := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

end Work.WilG4a.CD
