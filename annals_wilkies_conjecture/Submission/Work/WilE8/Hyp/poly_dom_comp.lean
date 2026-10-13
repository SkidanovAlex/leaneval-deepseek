import Mathlib

namespace Work.WilE8.Hyp

/-- The affine substitution `X ↦ 5 * n + 1 + n * X`, as a polynomial over `ℕ`. -/
noncomputable def affineSubst (n : ℕ) : Polynomial ℕ :=
  Polynomial.C (5 * n + 1) + Polynomial.C n * Polynomial.X

@[simp]
theorem affineSubst_eval (n d : ℕ) : (affineSubst n).eval d = 5 * n + 1 + n * d := by
  simp only [affineSubst, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

theorem poly_dom_comp (P : Polynomial ℕ) (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ d : ℕ,
      P.eval (5 * n + 1 + n * d) * (5 * n + 1 + n * d) ≤ p.eval d := by
  refine ⟨P.comp (affineSubst n) * affineSubst n, fun d => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_comp, affineSubst_eval]

end Work.WilE8.Hyp
