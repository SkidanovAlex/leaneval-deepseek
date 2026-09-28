import Mathlib
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.taylorDefs

namespace Work.Q44Geom

/-- Evaluating the formal `ℚ`-algebra homomorphism `taylorHom z b₁ b₂` at the two
directional parameters `u` is the same as evaluating the original polynomial at the
corresponding point `z + u 0 • b₁ + u 1 • b₂`.  Specialised to `z = substPoint w b₁ b₂ p 0`,
this says that the two-parameter Taylor expansion of `f` about the point `p ↦ Σ p_a w_a`,
evaluated at `u`, agrees with `f` evaluated at `p ↦ Σ p_a w_a + u 0 b₁ + u 1 b₂`. -/
theorem evalTaylorHom (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (p : Fin 3 → ℚ) (u : Fin 2 → ℚ) :
    MvPolynomial.eval u (Work.Q44Geom.taylorHom (Work.Q44Geom.substPoint w b₁ b₂ p 0) b₁ b₂ f)
      = MvPolynomial.eval (Work.Q44Geom.substPoint w b₁ b₂ p u) f := by
  -- Rewrite the outer evaluation as the algebra homomorphism `aeval u` and push it through
  -- the inner `aeval (taylorSubst ...)` using the universal property of `MvPolynomial`.
  have h1 : MvPolynomial.eval u (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f)
      = MvPolynomial.aeval
          (fun i => MvPolynomial.eval u (taylorSubst (substPoint w b₁ b₂ p 0) b₁ b₂ i)) f := by
    rw [taylorHom]
    exact MvPolynomial.comp_aeval_apply (taylorSubst (substPoint w b₁ b₂ p 0) b₁ b₂)
      (MvPolynomial.aeval u) f
  -- The residual substitution function is exactly the point `substPoint w b₁ b₂ p u`.
  have hfun : (fun i => MvPolynomial.eval u (taylorSubst (substPoint w b₁ b₂ p 0) b₁ b₂ i))
      = substPoint w b₁ b₂ p u := by
    funext i
    simp only [substPoint, taylorSubst, map_add, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Pi.zero_apply]
    ring
  rw [h1, hfun]
  rfl

end Work.Q44Geom
