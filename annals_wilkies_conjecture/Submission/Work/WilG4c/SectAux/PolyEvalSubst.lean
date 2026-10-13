import Mathlib

namespace Work.WilG4c.SectAux

/-- **Substituting a two-variable natural polynomial into a one-variable one.**

Given `b : ℕ[X]` and `q : ℕ[X₀,X₁]` there is a two-variable polynomial `b'` whose value at
`(x, y)` is the value of `b` at the value of `q` at `(x, y)`: the composite
`b'(X₀, X₁) = b(q(X₀, X₁))`.

Concretely `b' = b.eval₂ C q = (b.map C).eval q`, and the identity is the functoriality of
`Polynomial.eval₂` under a ring homomorphism (`Polynomial.hom_eval₂`). -/
theorem PolyEvalSubst (b : Polynomial ℕ) (q : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ x y : ℕ,
      MvPolynomial.eval ![x, y] b' = b.eval (MvPolynomial.eval ![x, y] q) := by
  refine ⟨Polynomial.eval₂ MvPolynomial.C q b, ?_⟩
  intro x y
  have h := Polynomial.hom_eval₂ (p := b) (f := MvPolynomial.C)
    (g := (MvPolynomial.eval ![x, y])) q
  rw [h]
  have hcomp : (MvPolynomial.eval ![x, y]).comp MvPolynomial.C = RingHom.id ℕ := by
    ext a
    simp
  rw [hcomp, Polynomial.eval₂_id]

end Work.WilG4c.SectAux
