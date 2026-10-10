import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

/-- The structure map `resMap 𝕜 X x : 𝕜 →+* κ(x)` factors through the global evaluation map
`X.Γevaluation x` of `Γ(X, ⊤)`. -/
lemma resMap_eq_hom (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) :
    resMap 𝕜 X x =
      (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv) ≫ (X ↘ Spec (.of 𝕜)).appTop ≫
        X.Γevaluation x).hom := by
  rw [resMap]
  rw [show X.Γevaluation x = X.presheaf.germ ⊤ x trivial ≫ X.residue x from rfl]

/-- Naturality of `resMap`: for a morphism `f : X ⟶ Y` over `𝕜` the induced compositum
`κ(f x) → κ(x)` intertwines the structure maps. -/
lemma resMap_naturality {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] (f : X ⟶ Y)
    (hf : f ≫ (Y ↘ Spec (.of 𝕜)) = (X ↘ Spec (.of 𝕜))) (x : X) :
    (f.residueFieldMap x).hom.comp (resMap 𝕜 Y (f x)) = resMap 𝕜 X x := by
  rw [resMap_eq_hom 𝕜 Y (f x), resMap_eq_hom 𝕜 X x]
  rw [show (f.residueFieldMap x).hom.comp
        (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (Y ↘ Spec (.of 𝕜)).appTop ≫
          Y.Γevaluation (f x)).hom)
      = (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (Y ↘ Spec (.of 𝕜)).appTop ≫
          Y.Γevaluation (f x)) ≫ f.residueFieldMap x).hom from rfl]
  rw [show ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (Y ↘ Spec (.of 𝕜)).appTop ≫
          Y.Γevaluation (f x)) ≫ f.residueFieldMap x
      = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (.of 𝕜)).appTop ≫
          X.Γevaluation x from by
    rw [Category.assoc (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv
          ((Y ↘ Spec (.of 𝕜)).appTop ≫ Y.Γevaluation (f x)) (f.residueFieldMap x),
      Category.assoc (Y ↘ Spec (.of 𝕜)).appTop (Y.Γevaluation (f x)) (f.residueFieldMap x),
      Scheme.Γevaluation_naturality f x,
      ← Category.assoc (Y ↘ Spec (.of 𝕜)).appTop f.appTop (X.Γevaluation x),
      ← Scheme.Hom.comp_appTop f (Y ↘ Spec (.of 𝕜)),
      hf]]

/-- A morphism over `𝕜` whose residue-field map at `x` is an isomorphism (e.g. an open
immersion or an isomorphism) induces a `𝕜`-algebra isomorphism `κ(f x) ≅ κ(x)`. -/
theorem resEquiv_of_morphism {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    (f : X ⟶ Y) (hf : f ≫ (Y ↘ Spec (.of 𝕜)) = (X ↘ Spec (.of 𝕜))) (x : X)
    [IsIso (f.residueFieldMap x)] :
    ResEquiv 𝕜 (f x) x := by
  refine ⟨(asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv, ?_⟩
  change (f.residueFieldMap x).hom.comp (resMap 𝕜 Y (f x)) = resMap 𝕜 X x
  exact resMap_naturality f hf x

end Work.Motivic
