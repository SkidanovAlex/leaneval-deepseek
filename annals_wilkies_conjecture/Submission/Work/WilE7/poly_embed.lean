import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

/-- The one-variable polynomial algebra `ℕ[X]` embeds into `MvPolynomial (Fin 2) ℕ` by
sending `X` to the first variable.  Evaluation of the image at `v : Fin 2 → ℕ` is
evaluation of `q` at `v 0`, so the second coordinate is irrelevant. -/
lemma eval_aeval_X_zero (q : Polynomial ℕ) (v : Fin 2 → ℕ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) q) = q.eval (v 0) := by
  have h := Polynomial.aeval_algHom_apply
      (f := (MvPolynomial.aeval v : MvPolynomial (Fin 2) ℕ →ₐ[ℕ] ℕ))
      (x := MvPolynomial.X (0 : Fin 2)) (p := q)
  simp only [MvPolynomial.aeval_X] at h
  rw [← MvPolynomial.aeval_eq_eval, ← h]
  rfl

theorem poly_embed :
    (∀ q : Polynomial ℕ, ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ, b.eval ![D, k] = q.eval D) ∧
    (∀ b₁ b₂ : MvPolynomial (Fin 2) ℕ, ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
        b.eval ![D, k] = b₁.eval ![D, k] + b₂.eval ![D, k]) ∧
    (∀ b : MvPolynomial (Fin 2) ℕ, ∀ q : Polynomial ℕ,
        ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
          b'.eval ![D, k] = b.eval ![D, k] * q.eval D) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Every one-variable polynomial comes from a two-variable polynomial ignoring `k`.
    intro q
    exact ⟨Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) q, fun D k => by
      have h := eval_aeval_X_zero q (![D, k] : Fin 2 → ℕ)
      rwa [show (![D, k] : Fin 2 → ℕ) 0 = D from by simp] at h⟩
  · -- The two-variable polynomials are closed under addition.
    intro b₁ b₂
    exact ⟨b₁ + b₂, fun D k => by simp⟩
  · -- ... and under multiplication by the image of a one-variable polynomial.
    intro b q
    refine ⟨b * Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) q, fun D k => ?_⟩
    have h := eval_aeval_X_zero q (![D, k] : Fin 2 → ℕ)
    rw [show (![D, k] : Fin 2 → ℕ) 0 = D from by simp] at h
    simp only [map_mul, h]

end Work.WilE7
