import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Limits

set_option linter.style.haveILetI false

/-- **The affine chart `U ≅ Spec Γ(X,U)` of an open subscheme is a morphism over `Spec 𝕜`.**

For a `𝕜`-scheme `X`, an affine open `U ⊆ X` (with the `𝕜`-algebra structure on `Γ(X,U)` given by
the structure morphism `𝕜 → Γ(X,U)`), the isomorphism `hU.isoSpec : ↑U ≅ Spec Γ(X,U)` commutes with
the structure morphisms: `hU.isoSpec.hom ≫ Spec.map (algebraMap 𝕜 Γ(X,U)) = U.ι ≫ (X ↘ Spec 𝕜)`.

Suggested route: `hU.isoSpec.hom = U.toSpecΓ`, then
`Scheme.Opens.toSpecΓ_SpecMap_appLE` / `IsAffineOpen.SpecMap_appLE_fromSpec` (both in Mathlib),
`IsAffineOpen.isoSpec_hom_fromSpec` and `Scheme.isoSpec_Spec_inv` close it.  An identical
computation is already on disk in `Submission/Work/K3Inputs/cylFieldAlgEquiv.lean`
(`chart_structure_eq_gen`) and `Submission/Work/CrauderKatz/sections_preimage_fst_pullback_affineOpen.lean`. -/
theorem isoSpec_over (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra 𝕜 ↥(X.presheaf.obj (Opposite.op U)) :=
      ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom.toAlgebra
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ↥(X.presheaf.obj (Opposite.op U))))
      = U.ι ≫ (X ↘ Spec (CommRingCat.of 𝕜)) := by
  letI : Algebra 𝕜 ↥(X.presheaf.obj (Opposite.op U)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom.toAlgebra
  -- The structure morphism of the affine chart `Spec Γ(X,U)` is `hU.fromSpec` followed by `X ↘ Spec 𝕜`.
  have key : Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ↥(X.presheaf.obj (Opposite.op U))))
      = hU.fromSpec ≫ (X ↘ Spec (CommRingCat.of 𝕜)) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (X := X) (Y := Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) (isAffineOpen_top (Spec (CommRingCat.of 𝕜))) hU
      (le_top : U ≤ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [RingHom.algebraMap_toAlgebra]
    rw [← h, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.ofHom_hom
      ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top)).symm
  -- `hU.isoSpec.hom` inverts `hU.fromSpec` onto the open immersion `U.ι`.
  rw [key, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

end Work.CY3Stab.Prod
