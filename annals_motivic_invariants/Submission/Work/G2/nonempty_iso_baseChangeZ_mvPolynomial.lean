import Mathlib
import Submission.Work.G2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.nonempty_iso_baseChangeZ_mvPolynomial`

The affine space `𝔸^n_ℤ = Spec (MvPolynomial (Fin n) ℤ)` base changes along `Spec 𝕜 ⟶ Spec ℤ` to
the affine space `𝔸^n_𝕜 = Spec (MvPolynomial (Fin n) 𝕜)`.

Concretely, `pullbackSpecIso ℤ 𝕜 (MvPolynomial (Fin n) ℤ)` identifies the fibred product
`Spec (MvPolynomial (Fin n) ℤ) ×_{Spec ℤ} Spec 𝕜` — which is `Work.G2.baseChangeZ 𝕜` of the affine
space — with `Spec (𝕜 ⊗[ℤ] MvPolynomial (Fin n) ℤ)`, and the base-change-of-coefficients algebra
equivalence `MvPolynomial.algebraTensorAlgEquiv ℤ 𝕜 : 𝕜 ⊗[ℤ] MvPolynomial (Fin n) ℤ ≃ₐ[𝕜]
MvPolynomial (Fin n) 𝕜` transports this to `Spec (MvPolynomial (Fin n) 𝕜)`.
-/

set_option autoImplicit false

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem nonempty_iso_baseChangeZ_mvPolynomial (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Nonempty (Work.G2.baseChangeZ 𝕜 (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) ℤ))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) 𝕜))) :=
  ⟨(pullbackSpecIso ℤ 𝕜 (MvPolynomial (Fin n) ℤ)).trans
    (Scheme.Spec.mapIso ((RingEquiv.toCommRingCatIso
      (MvPolynomial.algebraTensorAlgEquiv ℤ 𝕜).toRingEquiv).op).symm)⟩

end Work.G2
