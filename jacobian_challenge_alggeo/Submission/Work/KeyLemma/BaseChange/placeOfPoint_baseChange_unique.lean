import Mathlib
import Submission.Work.KeyLemma.BaseChange
import Submission.Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange
import Submission.Work.KeyLemma.Place.placeOfPoint_degree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Uniqueness of the place of `C_L` over a `k`-rational point of `C`

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let `L/k` be a
field extension and let `p : Spec k ⟶ C` be a `k`-point of `C`, with image the place
`q = placeOfPoint C p`.  The base change `p_L = Pt.baseChange L p : Spec L ⟶ C_L` is an
`L`-point of `C_L = C ×_k Spec L` whose image `placeOfPoint C_L p_L` is a place of `C_L`
lying over `q` (`proj_placeOfPoint_baseChange`).

This file proves that it is the *unique* such place: every place `Q'` of `C_L` whose
projection to `C` is (the underlying point of) `q` is `placeOfPoint C_L p_L`.

The mathematical content is that the fibre of the projection `C_L ⟶ C` over a `k`-rational
point is a single point: it is `Spec (κ(q) ⊗_k L)` and `κ(q) = k` because `q` is the image
of a `k`-point (this is `Work.KeyLemma.Place.placeOfPoint_degree`).  Formally:

* `isIsoResidueFieldMap_placeOfPoint`: the residue field map `κ(k) = κ(q) ⟶ κ(q)` at such a
  point is an isomorphism -- the `k`-point is a section, hence splits `C.hom` on residue
  fields, and a bijective ring homomorphism of fields is an isomorphism;
* `subsingleton_spec_tensor`: for any point `z` of the fibre product with `fst z = q.point`,
  the tensor product `κ(fst z) ⊗_{κ(snd z)} κ(pt)` of the corresponding triplet is a field
  (its spectrum is a subsingleton), because one of the two structure maps is the isomorphism
  above and the pullback square `Spec (κ(fst z) ⊗ ⋯) ⟶ Spec κ(fst z) ↓ Spec κ(snd z)`
  then has an isomorphic vertical leg;
* `eq_point_of_baseChangeFst_eq` and finally `placeOfPoint_baseChange_unique`: the points of
  the fibre of `C_L ⟶ C` over `q.point` are unique, via the parametrisation
  `Scheme.Pullback.SpecTensorTo` of the fibre product.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.KeyLemma.BaseChange

universe u

/-- The residue field map `κ(q) ⟶ κ(q)` at the place `q = placeOfPoint C p` of a
`k`-rational point is an isomorphism: a `k`-point is a section of the structure morphism
`C.hom`, so `C.hom.residueFieldMap q.point` has a retraction and a section, hence is
bijective. -/
theorem isIsoResidueFieldMap_placeOfPoint {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) :
    IsIso (C.hom.residueFieldMap (Work.KeyLemma.Curve.placeOfPoint C p).point) := by
  set z : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  set s : Spec (CommRingCat.of k) ⟶ C.left := Work.KeyLemma.Curve.Pt.leftHom p
  change IsIso (C.hom.residueFieldMap (s z))
  have hsec : s ≫ C.hom = 𝟙 (Spec (CommRingCat.of k)) := Work.KeyLemma.Curve.Pt.leftHom_comp p
  have hpoint : C.hom (s z) = z := Subsingleton.elim _ _
  -- the composite of the residue field maps of the section and of the structure morphism is
  -- an isomorphism, being the residue field map of the identity
  have hcomp : C.hom.residueFieldMap (s z) ≫ s.residueFieldMap z
      = (Scheme.residueFieldCongr hpoint).hom := by
    rw [← Scheme.residueFieldMap_comp]
    rw [Scheme.Hom.residueFieldMap_congr hsec z]
    simp
  haveI : IsIso (C.hom.residueFieldMap (s z) ≫ s.residueFieldMap z) := by
    rw [hcomp]; infer_instance
  -- a ring homomorphism of fields is injective; the composite is surjective, so it is too
  have hsurj : Function.Surjective (s.residueFieldMap z) :=
    Function.Surjective.of_comp (ConcreteCategory.bijective_of_isIso
      (C.hom.residueFieldMap (s z) ≫ s.residueFieldMap z)).2
  haveI : IsIso (s.residueFieldMap z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective _, hsurj⟩
  exact IsIso.of_isIso_comp_right (C.hom.residueFieldMap (s z)) (s.residueFieldMap z)

/-- **The `κ(snd) ⊗_{κ(fst)} κ`-description of the fibres of the base change over a rational
point is a field.**  For a point `T` of the fibre product `C_L = C ×_k Spec L` whose image in
`C` is the `k`-rational place `q = placeOfPoint C p`, the spectrum of the tensor product
`κ(T.x) ⊗_{κ(T.s)} κ(T.y)` is a subsingleton. -/
theorem subsingleton_spec_tensor {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) (L : Type u) [Field L] [Algebra k L]
    (T : Scheme.Pullback.Triplet C.hom (Work.CurveBasics.Curve.specMap k L))
    (hx : T.x = (Work.KeyLemma.Curve.placeOfPoint C p).point) :
    Subsingleton ↥(Spec T.tensor) := by
  -- one leg of the pullback square describing `Spec T.tensor` is an isomorphism
  haveI : IsIso (C.hom.residueFieldMap T.x) := by
    rw [hx]; exact isIsoResidueFieldMap_placeOfPoint C p
  have hpb := Scheme.Pullback.Triplet.isPullback_SpecMap_tensor T
  haveI : IsIso (Spec.map ((Scheme.residueFieldCongr T.hx).inv
      ≫ Scheme.Hom.residueFieldMap C.hom T.x)) := inferInstance
  -- hence the vertical leg `Spec T.tensor ⟶ Spec κ(T.y)` is an isomorphism
  have hIso : IsIso (Spec.map T.tensorInr) := hpb.isIso_snd_of_isIso
  -- and `Spec κ(T.y)` is the spectrum of a field
  haveI : Subsingleton ↥(Spec ((Spec (CommRingCat.of L)).residueField T.y)) := inferInstance
  exact Equiv.subsingleton (Scheme.Hom.homeomorph (Spec.map T.tensorInr)).toEquiv

/-- **The fibre of the base change `C_L ⟶ C` over a `k`-rational point is a single point.**
Every point of `C_L` projecting to `q.point = (placeOfPoint C p).point` is the image of the
closed point of `Spec L` under the base changed point `Pt.baseChange L p`. -/
theorem eq_point_of_baseChangeFst_eq {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (L : Type u) [Field L] [Algebra k L] (p : Work.KeyLemma.Curve.Point C)
    (z : ↥(Work.CurveBasics.Curve.baseChangeLeft C L))
    (hz : Work.CurveBasics.Curve.baseChangeFst C L z =
      (Work.KeyLemma.Curve.placeOfPoint C p).point) :
    z = Work.KeyLemma.Curve.Pt.leftHom (Work.KeyLemma.Curve.Pt.baseChange L p)
      (IsLocalRing.closedPoint L) := by
  let z₀ : ↥(Work.CurveBasics.Curve.baseChangeLeft C L) :=
    Work.KeyLemma.Curve.Pt.leftHom (Work.KeyLemma.Curve.Pt.baseChange L p)
      (IsLocalRing.closedPoint L)
  change z = z₀
  -- the base changed point projects to `q.point` as well
  have hz₀ : Work.CurveBasics.Curve.baseChangeFst C L z₀ =
      (Work.KeyLemma.Curve.placeOfPoint C p).point :=
    Work.KeyLemma.BaseChange.proj_placeOfPoint_baseChange C L p
  -- the two points live in the same fibre of the parametrisation of the fibre product
  let T : Scheme.Pullback.Triplet C.hom (Work.CurveBasics.Curve.specMap k L) :=
    Scheme.Pullback.Triplet.ofPoint z
  let T₀ : Scheme.Pullback.Triplet C.hom (Work.CurveBasics.Curve.specMap k L) :=
    Scheme.Pullback.Triplet.ofPoint z₀
  have hxT : T.x = (Work.KeyLemma.Curve.placeOfPoint C p).point := hz
  have hxT₀ : T₀.x = (Work.KeyLemma.Curve.placeOfPoint C p).point := hz₀
  -- the fibre of `C_L ⟶ C` over `q.point` has a single point
  haveI : Subsingleton ↥(Spec T.tensor) := subsingleton_spec_tensor C p L T hxT
  have hT : T = T₀ := Scheme.Pullback.Triplet.ext (by rw [hxT, hxT₀]) (Subsingleton.elim _ _)
  -- both points are the image of the unique point of `Spec T.tensor` under `SpecTensorTo`
  have e1 : T.SpecTensorTo (Scheme.Pullback.SpecOfPoint z) = z :=
    Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  have e2 : T₀.SpecTensorTo (Scheme.Pullback.SpecOfPoint z₀) = z₀ :=
    Scheme.Pullback.SpecTensorTo_SpecOfPoint z₀
  rw [← e1, ← e2]
  have hspec : Spec.map (Scheme.Pullback.Triplet.tensorCongr hT).hom ≫ T.SpecTensorTo =
      T₀.SpecTensorTo := Scheme.Pullback.tensorCongr_SpecTensorTo hT
  rw [← hspec, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

theorem placeOfPoint_baseChange_unique {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (L : Type u) [Field L] [Algebra k L] (p : Work.KeyLemma.Curve.Point C)
    (Q' : (Work.CurveBasics.Curve.baseChange C L).Place)
    (hQ' : Work.CurveBasics.Curve.baseChangeFst C L Q'.point =
      (Work.KeyLemma.Curve.placeOfPoint C p).point) :
    Q' = Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
      (Work.KeyLemma.Curve.Pt.baseChange L p) := by
  apply Subtype.ext
  exact eq_point_of_baseChangeFst_eq C L p Q'.point hQ'

end Work.KeyLemma.BaseChange
