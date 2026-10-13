import Mathlib

namespace Work.WilG4c

/-- Substituting `D ↦ dT(D,r)` into a one-variable degree polynomial: the bivariate polynomial
`B` with `eval ![D,r] B = b.eval (eval ![D,r] dT)` for all `D r`.  (Take
`B := Polynomial.eval₂ MvPolynomial.C dT b` and use `Polynomial.hom_eval₂` together with
`MvPolynomial.eval_C` and `Polynomial.eval₂_id`.) -/
theorem polyComposeD (b : Polynomial ℕ) (dT : MvPolynomial (Fin 2) ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ,
      ∀ D r : ℕ, MvPolynomial.eval ![D, r] B = b.eval (MvPolynomial.eval ![D, r] dT) := by
  -- `eval₂` along the constant embedding `C` of coefficients into the bivariate ring: this is
  -- the composition of `b` with `dT`, and evaluation at `![D,r]` commutes with it.
  refine ⟨Polynomial.eval₂ MvPolynomial.C dT b, fun D r => ?_⟩
  have h := Polynomial.hom_eval₂ b MvPolynomial.C (MvPolynomial.eval ![D, r]) dT
  rw [h]
  -- evaluating a constant coefficient at `![D,r]` returns it, so the coefficient map is the
  -- identity of `ℕ`.
  have h2 : (MvPolynomial.eval ![D, r]).comp MvPolynomial.C = RingHom.id ℕ := by
    ext n
    simp
  rw [h2, Polynomial.eval₂_id]

end Work.WilG4c
