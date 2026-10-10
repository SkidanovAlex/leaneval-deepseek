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
# `Work.CY3.exists_theta_of_resEquiv`

`ResEquiv 𝕜 (genericPoint X) (genericPoint Y)` says that the residue fields of the two schemes
at their generic points are isomorphic as `𝕜`-algebras.  The residue field `κ(η_X)` of an
integral scheme at its generic point is the function field `κ(X) = 𝒪_{X,η_X}`: the residue map at
a point whose stalk is a field is an isomorphism.

This file proves that the `𝕜`-algebra isomorphism `κ(η_X) ≅ κ(η_Y)` supplied by `ResEquiv`
transports to a *ring* isomorphism of the function fields `κ(X) ≃+* κ(Y)`, compatible with the
`𝕜`-algebra structures (`Work.CY3.structMap`) in the sense recorded in the statement: the
inverse of the ring isomorphism intertwines the two structure maps.

The bridge between the function field and the residue field of the generic point is the canonical
`residueFieldSelfEquiv` of `Submission/Work/CY3/GenericPointAux.lean`, whose inverse is the
residue map `IsLocalRing.residue`:

* `residueFieldSelfEquiv_symm_apply_structMap`: applying `α_X⁻¹` to `structMap 𝕜 X a` gives
  `resMap 𝕜 X η_X a` (the `𝕜`-structure of `κ(η_X)`);
* `residueFieldSelfEquiv_resMap_apply`: applying `α_X` to `resMap 𝕜 X η_X a` gives back
  `structMap 𝕜 X a`.

Both are immediate from `residueFieldSelfEquiv_symm_toRingHom` / `residueFieldSelfEquiv_residue`
together with the definitional identity `resMap 𝕜 X η_X = (X.residue η_X).hom ∘ structMap 𝕜 X`
(`resMap_eq_residue_comp_structMap`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.CY3

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The canonical isomorphism `κ(X) ≃+* κ(η_X)` sends the structure map to `resMap`.**  For an
integral `𝕜`-scheme `X`, the inverse of `residueFieldSelfEquiv X.functionField` — that is, the
residue map `IsLocalRing.residue` at the generic point — carries the `𝕜`-algebra structure
`structMap 𝕜 X` of the function field to the `𝕜`-algebra structure `resMap 𝕜 X η_X` of the
residue field of the generic point. -/
lemma residueFieldSelfEquiv_symm_apply_structMap {𝕜 : Type} [Field 𝕜] (X : Scheme.{0})
    [IrreducibleSpace X] [IsIntegral X] [X.Over (Spec (CommRingCat.of 𝕜))] (a : 𝕜) :
    (residueFieldSelfEquiv X.functionField).symm (structMap 𝕜 X a) =
      resMap 𝕜 X (genericPoint X) a := by
  rw [show resMap 𝕜 X (genericPoint X) a =
      IsLocalRing.residue X.functionField (structMap 𝕜 X a) from rfl]
  exact RingHom.congr_fun (residueFieldSelfEquiv_symm_toRingHom X.functionField)
    (structMap 𝕜 X a)

/-- **The canonical isomorphism `κ(η_X) ≃+* κ(X)` inverts `resMap` against the structure map.**
This is the inverse direction of `residueFieldSelfEquiv_symm_apply_structMap`. -/
lemma residueFieldSelfEquiv_resMap_apply {𝕜 : Type} [Field 𝕜] (X : Scheme.{0})
    [IrreducibleSpace X] [IsIntegral X] [X.Over (Spec (CommRingCat.of 𝕜))] (a : 𝕜) :
    residueFieldSelfEquiv X.functionField (resMap 𝕜 X (genericPoint X) a) = structMap 𝕜 X a := by
  rw [show resMap 𝕜 X (genericPoint X) a =
      IsLocalRing.residue X.functionField (structMap 𝕜 X a) from rfl]
  exact residueFieldSelfEquiv_residue X.functionField (structMap 𝕜 X a)

/-- **A `𝕜`-algebra isomorphism of the residue fields at the generic points lifts to a ring
equivalence of the function fields, intertwining the structure maps.**

`ResEquiv 𝕜 η_X η_Y` provides `e : κ(η_X) ≃+* κ(η_Y)` compatible with the structure maps
`resMap 𝕜 · η_·`; composing `e` with the canonical identifications
`κ(X) ≅ κ(η_X)` and `κ(η_Y) ≅ κ(Y)` yields `θ : κ(X) ≃+* κ(Y)`, and the two compatibility
lemmas above plus `he` show that `θ⁻¹` intertwines the two structure maps `structMap 𝕜 ·`. -/
theorem exists_theta_of_resEquiv {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of 𝕜))] [Y.Over (Spec (CommRingCat.of 𝕜))]
    (h : ResEquiv 𝕜 (genericPoint X) (genericPoint Y)) :
    ∃ θ : X.functionField ≃+* Y.functionField,
      (θ.symm.toRingHom).comp (Work.CY3.structMap 𝕜 Y) = Work.CY3.structMap 𝕜 X := by
  obtain ⟨e, he⟩ := h
  refine ⟨(residueFieldSelfEquiv X.functionField).symm.trans
    (e.trans (residueFieldSelfEquiv Y.functionField)), ?_⟩
  ext a
  change ((residueFieldSelfEquiv X.functionField).symm.trans
      (e.trans (residueFieldSelfEquiv Y.functionField))).symm ((structMap 𝕜 Y) a) =
    (structMap 𝕜 X) a
  have key : ((residueFieldSelfEquiv X.functionField).symm.trans
      (e.trans (residueFieldSelfEquiv Y.functionField))) (structMap 𝕜 X a) = structMap 𝕜 Y a := by
    change (residueFieldSelfEquiv Y.functionField)
        (e ((residueFieldSelfEquiv X.functionField).symm ((structMap 𝕜 X) a))) =
      (structMap 𝕜 Y) a
    rw [residueFieldSelfEquiv_symm_apply_structMap,
      show e (resMap 𝕜 X (genericPoint X) a) = resMap 𝕜 Y (genericPoint Y) a from
        RingHom.congr_fun he a,
      residueFieldSelfEquiv_resMap_apply]
  rw [← key, RingEquiv.symm_apply_apply]

end Work.CY3
