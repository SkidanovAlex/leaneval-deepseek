import Mathlib
import Submission.Work.MotR.Transcendental.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The scalar tower `𝔽 → Γ(X, U) → X.functionField`

For `X` an integral `𝔽`-scheme and `U ⊆ X` a nonempty open subscheme, the two algebra structures
`Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U : Algebra 𝔽 Γ(X, U)` and
`Work.FFResidual.overFunctionFieldAlgebra 𝔽 X : Algebra 𝔽 X.functionField` are compatible with the
canonical `Algebra Γ(X, U) X.functionField` (`Scheme.germToFunctionField U`, the restriction to the
generic point): they form a scalar tower.

Both structures factor through the sections `Γ(X, ⊤)`; the middle map of the tower
`Γ(X, U) → X.functionField` is the germ at the generic point `η`, so the comparison is the identity
`germ_U (map (≤ ⊤) s) = germ_⊤ s` of germs of sheaves on a topological space,
`TopCat.Presheaf.germ_res_apply`.

This is the section-ring analogue of
`Work.FFResidual.Geometry.isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory

namespace Work.MotR.Transcendental

-- Please declare this in namespace `Work.MotR.Transcendental`.
theorem isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra (𝔽 : Type) [Field 𝔽]
    (X : AlgebraicGeometry.Scheme) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝔽))]
    [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    letI := Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U
    letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
    IsScalarTower 𝔽 (X.presheaf.obj (Opposite.op U)) X.functionField := by
  letI := Work.MotR.Transcendental.overSectionAlgebra 𝔽 X U
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  -- the open set `⊤` is nonempty, so that `germToFunctionField ⊤` is available as an instance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  -- enough to compare the two `algebraMap`s on `𝔽`, keeping the middle one folded
  apply IsScalarTower.of_algebraMap_eq
  intro a
  -- the underlying element of `Γ(X, ⊤)` through which both structures factor
  set s := ConcreteCategory.hom (X ↘ Spec (CommRingCat.of 𝔽)).appTop
            (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv a) with hs
  -- the constants in the sections of `U`, as the restriction of `s`
  have h1 : algebraMap 𝔽 (X.presheaf.obj (Opposite.op U)) a
      = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply, hs]
  -- the same element of `Γ(X, ⊤)`, expanded into the function field at the generic point
  have h2 : algebraMap 𝔽 X.functionField a = X.germToFunctionField ⊤ s := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply, hs]
  rw [h1, h2]
  -- `algebraMap Γ(X, U) X.functionField` is the germ at the generic point, so the two sides are the
  -- germs of `s` at `η` computed in `⊤` and in `U`
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤))
    (genericPoint X) _ s).symm

end Work.MotR.Transcendental
