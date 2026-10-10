import Mathlib
import Submission.Work.CY3.GenericPointAux
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.structMap_fromSpecStalk`

The structure map of the function field `κ(X) = 𝒪_{X, η_X}` of an irreducible `𝕜`-scheme `X`
(`Work.CY3.structMap 𝕜 X : 𝕜 →+* κ(X)`) is the ring map corresponding to the canonical morphism
`X.fromSpecStalk η_X : Spec κ(X) ⟶ X` followed by the structure morphism `X ⟶ Spec 𝕜`:

`X.fromSpecStalk η_X ≫ (X ↘ Spec 𝕜) = Spec.map (ofHom (structMap 𝕜 X))`.

This is the statement that makes `structMap` usable at the level of morphisms of schemes: the
`𝕜`-algebra structure of the generic stalk (as opposed to `resMap 𝕜 X x`, the `𝕜`-structure of
the *residue* field of a point) is exactly the one induced by the structure morphism.
-/

set_option autoImplicit false
noncomputable section

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The canonical morphism `Spec κ(X) = Spec 𝒪_{X, η_X} ⟶ Spec 𝕜` induced by the structure
morphism `X ⟶ Spec 𝕜` and the canonical morphism `Spec 𝒪_{X, η_X} ⟶ X` from the generic stalk is
the one classified by the structure map `structMap 𝕜 X : 𝕜 →+* κ(X)` of the function field.

Equivalently: for the generic point `η = genericPoint X` of an irreducible `𝕜`-scheme `X`, the
`𝕜`-algebra structure of the stalk `𝒪_{X,η} = κ(X)` coming from the structure morphism of `X` is
the structure encoded by `Work.CY3.structMap`. -/
theorem structMap_fromSpecStalk (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [IrreducibleSpace X]
    [X.Over (Spec (CommRingCat.of 𝕜))] :
    X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (Work.CY3.structMap 𝕜 X)) := by
  -- The composite with the structure morphism `X ⟶ Spec 𝕜` corresponds, on global sections, to
  -- `f.appTop ≫ germ`: `fromSpecStalk_toSpecΓ` turns `fromSpecStalk` into `germ`, and
  -- `toSpecΓ_naturality` moves `toSpecΓ` across `f`.
  have h2 : X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (CommRingCat.of 𝕜)) ≫
        (Spec (CommRingCat.of 𝕜)).toSpecΓ =
      Spec.map ((X ↘ Spec (CommRingCat.of 𝕜)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial) := by
    rw [Scheme.toSpecΓ_naturality, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, Spec.map_comp]
  -- `Spec 𝕜` is affine, so `toSpecΓ` can be inverted: `toSpecΓ ≫ isoSpec.inv = 𝟙`.
  have h3 : X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map ((X ↘ Spec (CommRingCat.of 𝕜)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial) ≫
          (Spec (CommRingCat.of 𝕜)).isoSpec.inv := by
    rw [← h2]
    simp
  rw [h3, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  -- `Spec.map` of a composite is the reversed composite, so `(ΓSpecIso 𝕜).inv` moves to the front;
  -- the resulting ring map is `structMap 𝕜 X` by definition.
  rw [Work.CY3.structMap]
  congr 1

end Work.CY3
