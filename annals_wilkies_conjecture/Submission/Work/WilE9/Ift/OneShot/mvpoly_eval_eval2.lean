import Mathlib

namespace Work.WilE9.Ift.OneShot

/-- Substituting a two-variable polynomial into a univariate polynomial with nonnegative
integer coefficients commutes with evaluation. -/
theorem mvpoly_eval_eval2 {v : Fin 2 → ℕ} (d : MvPolynomial (Fin 2) ℕ) (p : Polynomial ℕ) :
    (MvPolynomial.eval v) (Polynomial.eval₂ MvPolynomial.C d p) =
      p.eval ((MvPolynomial.eval v) d) := by
  rw [Polynomial.hom_eval₂]
  have h : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℕ := by
    ext n
    simp
  rw [h, Polynomial.eval₂_id]

end Work.WilE9.Ift.OneShot
