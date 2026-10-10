import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Function fields of isomorphic irreducible schemes

The function field of an irreducible scheme `X` is the stalk `X.presheaf.stalk (genericPoint X)`
of the structure sheaf at the generic point. An isomorphism of schemes `e : X ≅ Y` restricts to
an isomorphism of the stalks at corresponding points, and an isomorphism of schemes carries the
generic point of `X` to the generic point of `Y` (a homeomorphism preserves generic points).
Combining the two gives the isomorphism of function fields.
-/

open AlgebraicGeometry CategoryTheory

namespace Work.CrauderKatz

/-- The stalk map of an isomorphism of schemes is an isomorphism of stalks. -/
noncomputable def stalkIsoOfIso {X Y : AlgebraicGeometry.Scheme.{0}} (e : X ≅ Y) (x : X) :
    Y.presheaf.stalk (e.hom x) ≅ X.presheaf.stalk x :=
  asIso (AlgebraicGeometry.Scheme.Hom.stalkMap e.hom x)

/-- An isomorphism of irreducible schemes carries the generic point of the source to the generic
point of the target. -/
lemma genericPoint_map_of_iso {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) : e.hom (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq ?_ (genericPoint_spec Y)
  have h := (genericPoint_spec X).image e.hom.continuous
  simpa using h

/-- Isomorphic irreducible schemes have isomorphic function fields of their structure sheaves. -/
noncomputable def functionFieldIso {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) :
    AlgebraicGeometry.Scheme.functionField X ≅ AlgebraicGeometry.Scheme.functionField Y :=
  (stalkIsoOfIso e (genericPoint X)).symm.trans
    (Y.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_map_of_iso e)))

/-- Function fields of isomorphic irreducible schemes are isomorphic. -/
theorem functionField_iso {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) :
    Nonempty ((AlgebraicGeometry.Scheme.functionField X : Type) ≃+*
      (AlgebraicGeometry.Scheme.functionField Y : Type)) := by
  refine ⟨RingEquiv.ofRingHom (functionFieldIso e).hom.hom (functionFieldIso e).inv.hom ?_ ?_⟩
  · ext x
    exact CommRingCat.hom_inv_apply (functionFieldIso e) x
  · ext x
    exact CommRingCat.inv_hom_apply (functionFieldIso e) x

end Work.CrauderKatz
