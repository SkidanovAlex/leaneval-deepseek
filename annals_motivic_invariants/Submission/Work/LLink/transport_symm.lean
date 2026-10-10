import Mathlib
import Submission.Work.LLink.Transport

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- The inverse of a transported birational map is the transport of the inverse along the
inverse identifications: `(ε ∘ ψ ∘ δ)⁻¹ = δ⁻¹ ∘ ψ⁻¹ ∘ ε⁻¹`. -/
theorem transport_symm {𝕜 : Type} [Field 𝕜] {S T : Scheme.{0}} [IrreducibleSpace S]
    [IrreducibleSpace T] (ε : (Affine3 𝕜).BirationalMap S) (ψ : S.BirationalMap T)
    (δ : T.BirationalMap (Affine3 𝕜)) :
    (transport ε ψ δ).symm = transport δ.symm ψ.symm ε.symm := by
  apply BirationalMap.ext
  simp only [transport_def, BirationalMap.symm_hom, BirationalMap.trans_hom, BirationalMap.trans_inv]
  rw [RationalMap.comp_assoc]

end Work.LLink
