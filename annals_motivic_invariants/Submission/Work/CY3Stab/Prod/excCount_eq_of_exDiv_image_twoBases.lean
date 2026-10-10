import Mathlib
import Submission.Work.CY3Stab.Prod.cInv_prodMap_of_exDiv_image

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

theorem excCount_eq_of_exDiv_image_twoBases (𝕜 : Type) [Field 𝕜]
    {X X' Y Y' : AlgebraicGeometry.Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace X'] [IrreducibleSpace Y] [IrreducibleSpace Y']
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [X'.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y'.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {S S' : AlgebraicGeometry.Scheme.{0}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [S'.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (z : S) (z' : S') (φ : X.BirationalMap Y) (ψ : X'.BirationalMap Y') (p : X → X')
    (hp : Function.Injective p) (h : exDiv ψ = p '' exDiv φ)
    (hr : ∀ x : X, ResEquiv 𝕜 (p x) z' ↔ ResEquiv 𝕜 x z) :
    excCount 𝕜 z' ψ = excCount 𝕜 z φ := by
  have hset : {w : X' | w ∈ exDiv ψ ∧ ResEquiv 𝕜 w z'}
      = p '' {x : X | x ∈ exDiv φ ∧ ResEquiv 𝕜 x z} := by
    ext w
    constructor
    · rintro ⟨hw, hres⟩
      rw [h] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨x, ⟨hx, (hr x).mp hres⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hres⟩, rfl⟩
      exact ⟨by rw [h]; exact ⟨x, hx, rfl⟩, (hr x).mpr hres⟩
  unfold excCount
  rw [hset, Set.ncard_image_of_injective _ hp]

end Work.CY3Stab.Prod
