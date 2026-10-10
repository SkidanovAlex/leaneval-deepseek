import Mathlib
import Submission.Work.FFResidual.Geometry.OverAlgebraDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The scalar tower `𝔽 → 𝒪_{X,z} → X.functionField`

For `X` an integral `𝔽`-scheme and `z : X`, the two algebra structures
`Work.FFResidual.overStalkAlgebra 𝔽 X z : Algebra 𝔽 (X.presheaf.stalk z)` and
`Work.FFResidual.overFunctionFieldAlgebra 𝔽 X : Algebra 𝔽 X.functionField` are compatible with the
canonical `Algebra (X.presheaf.stalk z) X.functionField` (the specialization map from the local ring
at `z` to the local ring at the generic point): they form a scalar tower.

Both structures factor through the sections `Γ(X, ⊤)`, the outer one as
`𝔽 → Γ(X, ⊤) → 𝒪_{X,z}` and the inner one as `𝔽 → Γ(X, ⊤) → X.functionField`; the compatibility of
the outer `algebraMap` with the middle one is exactly
`Scheme.algebraMap_germ_eq_germToFunctionField`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open AlgebraicGeometry CategoryTheory

namespace Work.FFResidual.Geometry

-- Please declare this in namespace `Work.FFResidual.Geometry`.
-- This replaces a failed attempt of the requester in `Geometry/OverAlgebra.lean` (now deleted); the
-- intended proof is `IsScalarTower.of_algebraMap_eq` + `Scheme.algebraMap_germ_eq_germToFunctionField`,
-- but the two sides need the `algebraMap` of the *middle* structure kept folded while the outer ones
-- are unfolded, which is where the other attempts got stuck.
theorem isScalarTower_overStalkAlgebra_overFunctionFieldAlgebra
    (𝔽 : Type) [Field 𝔽] (X : AlgebraicGeometry.Scheme)
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝔽))] [AlgebraicGeometry.IsIntegral X]
    (z : X) :
    letI := Work.FFResidual.overStalkAlgebra 𝔽 X z
    letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
    IsScalarTower 𝔽 (X.presheaf.stalk z) X.functionField := by
  letI := Work.FFResidual.overStalkAlgebra 𝔽 X z
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  -- the `Nonempty` instance of the open set `⊤` used by `germToFunctionField`, made explicit so
  -- that both sides of the final rewrite refer to the same germ.
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨z, trivial⟩⟩
  -- enough to compare the two `algebraMap`s on `𝔽`, keeping the middle `algebraMap` folded
  apply IsScalarTower.of_algebraMap_eq
  intro a
  -- the constants in the local ring at `z`, expanded into a germ at `z`
  have h1 : algebraMap 𝔽 (X.presheaf.stalk z) a
      = X.presheaf.germ ⊤ z trivial
          (ConcreteCategory.hom (X ↘ Spec (CommRingCat.of 𝔽)).appTop
            (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv a)) := by
    simp only [Work.FFResidual.overStalkAlgebra, RingHom.algebraMap_toAlgebra,
      ConcreteCategory.comp_apply]
  -- the same element of `Γ(X, ⊤)`, expanded into the function field through `germToFunctionField`
  have h2 : algebraMap 𝔽 X.functionField a
      = X.germToFunctionField ⊤
          (ConcreteCategory.hom (X ↘ Spec (CommRingCat.of 𝔽)).appTop
            (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of 𝔽)).inv a)) := by
    simp only [Work.FFResidual.overFunctionFieldAlgebra, RingHom.algebraMap_toAlgebra,
      ConcreteCategory.comp_apply]
  rw [h1, h2]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := ⊤) (x := z)
    (hx := trivial) _).symm

end Work.FFResidual.Geometry
