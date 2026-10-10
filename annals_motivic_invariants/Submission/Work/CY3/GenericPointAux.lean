import Mathlib
import ChallengeDeps
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary vocabulary for `Work.CY3.resEquiv_genericPoint_birationalMap`

This module sets up the two small pieces of vocabulary used by
`Work.CY3.resEquiv_genericPoint_birationalMap`:

* `Work.CY3.structMap 𝕜 X`: the structure map `𝕜 ⟶ κ(X) = 𝒪_{X, η_X}` of the function field of an
  irreducible `𝕜`-scheme, i.e. the `𝕜`-algebra structure that the *stalk at the generic point*
  carries (as opposed to `Work.Motivic.resMap 𝕜 X x`, which is the `𝕜`-structure of the *residue
  field* `κ(x)`).
* `Work.CY3.residueFieldSelfEquiv K`: the canonical identification `IsLocalRing.ResidueField K ≃+* K`
  of the residue field of a field `K` with `K` itself (Mathlib only has the residue *map*
  `IsLocalRing.residue K : K ⟶ IsLocalRing.ResidueField K`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The structure map of the function field.**  For an irreducible scheme `X` over `Spec 𝕜`, the
stalk `𝒪_{X, η_X} = κ(X)` at the generic point is a `𝕜`-algebra via the structure morphism
`X ⟶ Spec 𝕜`; this is that algebra structure, expressed as a ring homomorphism
`𝕜 →+* κ(X)`. -/
noncomputable def structMap (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [IrreducibleSpace X]
    [X.Over (Spec (CommRingCat.of 𝕜))] : 𝕜 →+* (X.functionField : Type) :=
  ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
    (X ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom

/-- **The residue field of a field is the field itself**, as a ring equivalence.  `K` is a local
ring (with maximal ideal `⊥`) and `IsLocalRing.ResidueField K = K ⧸ ⊥ = K`; the equivalence is the
map induced by `RingHom.id K`, which is bijective. -/
noncomputable def residueFieldSelfEquiv (K : Type) [Field K] :
    IsLocalRing.ResidueField K ≃+* K :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (RingHom.id K))
    ⟨RingHom.injective _, fun y => ⟨IsLocalRing.residue K y, by simp⟩⟩

/-- `residueFieldSelfEquiv K` is a section of the residue map: it inverts `IsLocalRing.residue`. -/
lemma residueFieldSelfEquiv_residue (K : Type) [Field K] (x : K) :
    residueFieldSelfEquiv K (IsLocalRing.residue K x) = x := by
  change (IsLocalRing.ResidueField.lift (RingHom.id K)) (IsLocalRing.residue K x) = x
  rw [← RingHom.comp_apply, IsLocalRing.ResidueField.lift_comp_residue]
  rfl

/-- The inverse of `residueFieldSelfEquiv K` is the residue map `K ⟶ IsLocalRing.ResidueField K`. -/
lemma residueFieldSelfEquiv_symm_toRingHom (K : Type) [Field K] :
    (residueFieldSelfEquiv K).symm.toRingHom = IsLocalRing.residue K := by
  ext x
  exact (RingEquiv.symm_apply_eq _).mpr (residueFieldSelfEquiv_residue K x)

/-- `Work.Motivic.resMap` at the generic point is the composite of the residue map
`X.residue η_X : κ(X) ⟶ κ(η_X)` with the structure map `structMap 𝕜 X : 𝕜 ⟶ κ(X)`. -/
lemma resMap_eq_residue_comp_structMap (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    [IrreducibleSpace X] [X.Over (Spec (CommRingCat.of 𝕜))] :
    resMap 𝕜 X (genericPoint X) =
      (X.residue (genericPoint X)).hom.comp (structMap 𝕜 X) := rfl

/-- **`ResEquiv` is symmetric**, in the sharpened form needed below: if `e` witnesses
`ResEquiv 𝕜 x z`, then `e.symm` witnesses that the structure maps agree in the other direction. -/
lemma resEquiv_symm {𝕜 : Type} [Field 𝕜] {X Z : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of 𝕜))] [Z.Over (Spec (CommRingCat.of 𝕜))] {x : X} {z : Z}
    (e : X.residueField x ≃+* Z.residueField z)
    (he : e.toRingHom.comp (resMap 𝕜 X x) = resMap 𝕜 Z z) :
    e.symm.toRingHom.comp (resMap 𝕜 Z z) = resMap 𝕜 X x := by
  rw [← he]
  ext a
  simp

end Work.CY3
