import Mathlib
import Submission.Work.Q44Geom.defs

set_option autoImplicit false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-- The substitution `X i ↦ z i + X 0 * b₁ i + X 1 * b₂ i`, giving two extra variables
for the two directional parameters. -/
def taylorSubst (z b₁ b₂ : Fin 5 → ℚ) : Fin 5 → MvPolynomial (Fin 2) ℚ :=
  fun i => C (z i) + X 0 * C (b₁ i) + X 1 * C (b₂ i)

/-- The `ℚ`-algebra homomorphism `f ↦ f(z + X₀ b₁ + X₁ b₂)` used for the two-parameter
Taylor expansion. -/
def taylorHom (z b₁ b₂ : Fin 5 → ℚ) :
    MvPolynomial (Fin 5) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  aeval (taylorSubst z b₁ b₂)

theorem taylorHom_apply (z b₁ b₂ : Fin 5 → ℚ) (f : MvPolynomial (Fin 5) ℚ) :
    taylorHom z b₁ b₂ f = aeval (taylorSubst z b₁ b₂) f := rfl

theorem taylorSubst_apply (z b₁ b₂ : Fin 5 → ℚ) (i : Fin 5) :
    taylorSubst z b₁ b₂ i = C (z i) + X 0 * C (b₁ i) + X 1 * C (b₂ i) := rfl

theorem taylorHom_X (z b₁ b₂ : Fin 5 → ℚ) (i : Fin 5) :
    taylorHom z b₁ b₂ (X i) = C (z i) + X 0 * C (b₁ i) + X 1 * C (b₂ i) := by
  simp [taylorHom, taylorSubst]

end Work.Q44Geom
