import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry

namespace Work.Domain.Engine

/-- In any category, `inv` of the inverse of an isomorphism is its forward map. -/
private lemma inv_iso_inv {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) :
    inv e.inv = e.hom :=
  IsIso.inv_eq_of_hom_inv_id (Iso.inv_hom_id e)

/-- For an open subset `U` of a scheme `X` and a point `x ∈ U`, the composite of
`Spec.map` of the isomorphism `𝒪_{X,x} ≅ 𝒪_{U,x}` with the canonical morphism
`Spec 𝒪_{U,x} ⟶ U` is the canonical morphism `U.fromSpecStalkOfMem x`, i.e. the defining
formula of `Scheme.Opens.fromSpecStalkOfMem`. -/
private lemma opens_stalkIso_fromSpecStalk {X : Scheme} (U : X.Opens) (x : U) :
    Spec.map (U.stalkIso x).hom ≫ U.toScheme.fromSpecStalk x = U.fromSpecStalkOfMem x.1 x.2 := by
  rw [Scheme.Opens.fromSpecStalkOfMem]
  simp only [← Scheme.Opens.stalkIso_inv]
  rw [inv_iso_inv (U.stalkIso ⟨x.1, x.2⟩)]

theorem fromSpecStalk {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g]
    (γ : Work.Domain.PartialMap.graph S g) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Spec.map (Work.Domain.PartialMap.theta g γ))
          (AlgebraicGeometry.Scheme.fromSpecStalk (Work.Domain.PartialMap.graph S g) γ))
        (Work.Domain.PartialMap.pr₂ S g) =
      AlgebraicGeometry.Scheme.PartialMap.fromFunctionField g := by
  rw [Work.Domain.PartialMap.theta]
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  rw [Work.Domain.PartialMap.germMapToFunctionField]
  rw [Work.Domain.PartialMap.toGraph_pr₂]
  rw [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem]
  set_option backward.isDefEq.respectTransparency false in
    rw [← Category.assoc, opens_stalkIso_fromSpecStalk]
  simp only [Work.Domain.PartialMap.etaDomain]

end Work.Domain.Engine
