import Mathlib
import Submission.Work.CurveBasics.Place.Coheight

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The residue degree of a place of a curve is positive

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let
`Q` be a place of `C`, i.e. a closed point of `C`.  We show that the residue degree
`[κ(Q) : κ(C.hom Q)]` is positive; in other words the residue field `κ(Q)` is a
*finite* extension of the residue field of the image point of `Q` in `Spec k`.

The mathematical content is the Nullstellensatz: a closed point of a scheme which is
locally of finite type over a field has residue field of finite degree over that field.
Concretely we show that the canonical morphism `Spec κ(Q) ⟶ Spec k` (the composite
`C.fromSpecResidueField Q.point ≫ C.hom`) is finite: since `Q` is closed,
`C.fromSpecResidueField Q.point` is locally of finite type
(`isClosed_singleton_iff_locallyOfFiniteType`), hence so is the composite, and since
the source is the spectrum of a field and the target `Spec k` is a Jacobson scheme, it
is finite (`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`).  Reading this
finiteness along the commutative square
`Spec.map (residueFieldMap) ≫ fromSpecResidueField = fromSpecResidueField ≫ f`
then gives the finiteness of the residue field extension `κ(C.hom Q) ⟶ κ(Q)`, so its
dimension over `κ(C.hom Q)` is positive.
-/

namespace Work.CurveBasics.Place

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

open Work.CurveBasics in
theorem residueDegree_pos {k : Type*} [Field k] {C : Curve k} (Q : C.Place) :
    0 < C.hom.residueDegree Q.point := by
  -- `Spec κ(Q) ⟶ Spec k` is locally of finite type: the first factor because `Q` is a
  -- closed point of the locally finite type `k`-scheme `C`, the second by hypothesis.
  have hloc : LocallyOfFiniteType (C.left.fromSpecResidueField Q.point) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp Q.isClosed
  -- A morphism from the spectrum of a field to a Jacobson scheme which is locally of
  -- finite type is finite.
  have hfin : IsFinite (C.left.fromSpecResidueField Q.point ≫ C.hom) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    exact inferInstance
  -- The corresponding ring homomorphism `k ⟶ κ(Q)` is finite.
  have hψ : (Spec.preimage (C.left.fromSpecResidueField Q.point ≫ C.hom)).hom.Finite := by
    rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
    exact hfin
  -- The factorization `Spec κ(Q) → Spec κ(C.hom Q) → Spec k` of that morphism.
  have hfac : C.left.fromSpecResidueField Q.point ≫ C.hom
      = Spec.map (C.hom.residueFieldMap Q.point) ≫
        (Spec (CommRingCat.of k)).fromSpecResidueField (C.hom Q.point) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField C.hom Q.point).symm
  have hsplit : (Spec.preimage (C.left.fromSpecResidueField Q.point ≫ C.hom)).hom
      = (C.hom.residueFieldMap Q.point).hom.comp
        (Spec.preimage ((Spec (CommRingCat.of k)).fromSpecResidueField (C.hom Q.point))).hom := by
    rw [hfac, Spec.preimage_comp, Spec.preimage_map]
    rfl
  -- Hence the residue field extension `κ(C.hom Q) ⟶ κ(Q)` is finite.
  have hg : (C.hom.residueFieldMap Q.point).hom.Finite := by
    refine RingHom.Finite.of_comp_finite (f :=
      (Spec.preimage ((Spec (CommRingCat.of k)).fromSpecResidueField (C.hom Q.point))).hom) ?_
    rw [← hsplit]
    exact hψ
  -- A finite nontrivial module over a field has positive dimension.
  let := (C.hom.residueFieldMap Q.point).hom.toAlgebra
  have : Module.Finite ((Spec (CommRingCat.of k)).residueField (C.hom Q.point))
      (C.left.residueField Q.point) := by
    rw [← RingHom.finite_algebraMap]
    exact hg
  rw [Scheme.Hom.residueDegree]
  exact Module.finrank_pos

end Work.CurveBasics.Place
