/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Submission.Work.DescentGeom.Derived
import Submission.Work.DescentGeom.geometricallyIrreducible_of_bc
import Submission.Work.DescentGeom.isSeparated_of_bc
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the geometric properties of the descended Jacobian

The group chunk `G'` is proper, smooth, geometrically irreducible over `k'` and has connected
underlying space.  Since `(D.J)_{k'} ≅ G'` and the projection `(D.J)_{k'} ⟶ D.J` is flat,
surjective and quasi-compact, `D.J` inherits these properties:

* `Smooth`, `LocallyOfFiniteType`, `UniversallyClosed` by fpqc descent
  (`MorphismProperty.of_pullback_snd_of_descendsAlong`, applied to the base change of `D.J.hom`
  along `Spec k' ⟶ Spec k`);
* `IsSeparated` by `Work.DescentGeom.isSeparated_of_bc`;
* `IsProper` from the three;
* `GeometricallyIrreducible` by `Work.DescentGeom.geometricallyIrreducible_of_bc`;
* `ConnectedSpace` from the surjection `G' ⟶ D.J`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory CategoryTheory.Obj
open CartesianMonoidalCategory Functor

universe u

namespace Work.DescentGeom

noncomputable section

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ### Transfer of the geometric properties along an isomorphism of base changes -/

/-- An isomorphism in `Over (Spec k')` induces an isomorphism of the underlying schemes. -/
theorem isIso_left_of_iso {X Y : Sch k'} (e : X ≅ Y) : IsIso e.hom.left :=
  ⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩

theorem smooth_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y) [Smooth Y.hom] :
    Smooth (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

theorem isProper_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y) [IsProper Y.hom] :
    IsProper (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

theorem locallyOfFiniteType_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y)
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

theorem universallyClosed_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y)
    [UniversallyClosed Y.hom] : UniversallyClosed (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

theorem isSeparated_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y)
    [IsSeparated Y.hom] : IsSeparated (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

theorem geomIrred_of_bcIso {X : Sch k} {Y : Sch k'} (e : bc k' X ≅ Y)
    [GeometricallyIrreducible Y.hom] : GeometricallyIrreducible (bc k' X).hom := by
  haveI := isIso_left_of_iso e
  rw [← Over.w e.hom]
  infer_instance

/-- A continuous surjection from a connected space has connected codomain. -/
theorem ConnectedSpace.of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] (f : X → Y) (hf : Function.Surjective f) (hc : Continuous f) :
    ConnectedSpace Y where
  isPreconnected_univ := by
    rw [← hf.range_eq, ← Set.image_univ]
    exact isPreconnected_univ.image f hc.continuousOn
  toNonempty := ⟨f (Classical.arbitrary X)⟩

end

namespace Input

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C} (D : Input C P0)

/-- `(D.J)_{k'}` is smooth over `k'`. -/
theorem smooth_bcJ : Smooth (bc D.k' D.J).hom := smooth_of_bcIso D.bcIso

/-- `(D.J)_{k'}` is locally of finite type over `k'`. -/
theorem locallyOfFiniteType_bcJ : LocallyOfFiniteType (bc D.k' D.J).hom :=
  locallyOfFiniteType_of_bcIso D.bcIso

/-- `(D.J)_{k'}` is universally closed over `k'`. -/
theorem universallyClosed_bcJ : UniversallyClosed (bc D.k' D.J).hom :=
  universallyClosed_of_bcIso D.bcIso

/-- `(D.J)_{k'}` is separated over `k'`. -/
theorem isSeparated_bcJ : IsSeparated (bc D.k' D.J).hom := isSeparated_of_bcIso D.bcIso

/-- `(D.J)_{k'}` is geometrically irreducible over `k'`. -/
theorem geomIrred_bcJ : GeometricallyIrreducible (bc D.k' D.J).hom := geomIrred_of_bcIso D.bcIso

/-- `D.J` is smooth over `k` (fpqc descent of smoothness). -/
theorem smooth_J : Smooth D.J.hom := by
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := D.J.hom) (g := Work.Descent.specMap k D.k')
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact smooth_bcJ D

/-- `D.J` is locally of finite type over `k` (fpqc descent). -/
theorem locallyOfFiniteType_J : LocallyOfFiniteType D.J.hom := by
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := @LocallyOfFiniteType)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := D.J.hom) (g := Work.Descent.specMap k D.k')
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact locallyOfFiniteType_bcJ D

/-- `D.J` is universally closed over `k` (fpqc descent). -/
theorem universallyClosed_J : UniversallyClosed D.J.hom := by
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := D.J.hom) (g := Work.Descent.specMap k D.k')
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact universallyClosed_bcJ D

/-- `D.J` is separated over `k`. -/
theorem isSeparated_J : IsSeparated D.J.hom :=
  @isSeparated_of_bc k D.k' _ _ _ D.J (isSeparated_bcJ D)

/-- `D.J` is proper over `k`. -/
theorem isProper_J : IsProper D.J.hom := by
  haveI := isSeparated_J D
  haveI := universallyClosed_J D
  haveI := locallyOfFiniteType_J D
  exact IsProper.mk

/-- `D.J` is geometrically irreducible over `k`. -/
theorem geomIrred_J : GeometricallyIrreducible D.J.hom :=
  @geometricallyIrreducible_of_bc k D.k' _ _ _ D.J (geomIrred_bcJ D)

/-- The underlying space of `D.J` is connected. -/
theorem connected_J : ConnectedSpace D.J.left := by
  haveI := geomIrred_J D
  haveI : IrreducibleSpace D.J.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := D.J.hom)
  infer_instance

end Input

end Work.DescentGeom
