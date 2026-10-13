import Mathlib
import Submission.Work.WilE7.poly_embed

namespace Work.WilE7

/-- Given a one-variable polynomial `p` (in the variable `D`), the two-variable polynomial
`q = X₁ · p(X₀)` satisfies `q(D, k) = k * p(D)`.  Consequently
`(4 * q + 3)^2 ∈ ℕ[X₀, X₁]` evaluates at `(D, k)` to `(4 * (k * p(D)) + 3)^2`. -/
theorem DimOneCellsPoly (p : Polynomial ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![D, k] b = (4 * (k * p.eval D) + 3) ^ 2 := by
  refine ⟨(4 * (MvPolynomial.X 1 * Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) p) + 3) ^ 2, ?_⟩
  intro D k
  have h := eval_aeval_X_zero p (![D, k] : Fin 2 → ℕ)
  rw [show (![D, k] : Fin 2 → ℕ) 0 = D from by simp] at h
  simp only [map_pow, map_add, map_mul, MvPolynomial.eval_X, h]
  simp

end Work.WilE7
