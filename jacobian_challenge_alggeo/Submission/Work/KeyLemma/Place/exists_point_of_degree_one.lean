/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A place of degree one is the image of a `k`-point

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k`.  This file
proves the converse of `Work.KeyLemma.Place.placeOfPoint_degree`:

> if `Q` is a place of `C` of degree one, then `Q = placeOfPoint C p` for a `k`-point
> `p : Spec k ⟶ C`.

Equivalently: a closed point of `C` whose residue field is one-dimensional over `k`
(hence equal to `k`) is a `k`-rational point.

## Proof

Let `x = Q.point` be the underlying point, so that `Q.degree = [κ(x) : k]`.  The hypothesis
`deg [Q] = 1` says exactly `Q.degree = 1` (`Curve.deg_place`), and
`Work.CurveBasics.Place.degree_eq_finrank` rewrites this as
`finrank k κ(x) = 1`.  Since the canonical map `k ⟶ κ(x)` is injective (`k` is a field and
`κ(x)` is nontrivial) and its source is one-dimensional, it is bijective
(`finrank_eq_one_iff_of_nonzero'`); equivalently the canonical morphism
`Spec κ(x) ⟶ Spec k` is an isomorphism.

It remains to turn this into a morphism `Spec k ⟶ C` over `Spec k`.  The key identity is
`Work.KeyLemma.Place.fromSpecResidueField_comp_hom`:

`C.left.fromSpecResidueField x ≫ C.hom = Spec.map (algebraMap k κ(x))`,

i.e. the composite of the canonical morphism `Spec κ(x) ⟶ C` with the structure morphism of
the curve is precisely the morphism on spectra of the canonical `k`-algebra structure on
`κ(x)`.  (This is the functoriality of residue fields,
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`, combined with the description of
`Spec.fromSpecResidueField` for the spectrum of the base field,
`Scheme.Spec.fromSpecStalk_eq`.)  As the algebra map is an isomorphism, inverting its spectrum
yields a morphism `Spec k ⟶ C` over `Spec k`, which is our point `p`; on points it is the
constant map at `x`, because `Spec κ(x)` is a single point
(`Scheme.fromSpecResidueField_apply`).  Hence `placeOfPoint C p = Q`.

Note that neither properness nor closedness of `x` is used: the argument works for any point
of a `k`-scheme whose residue degree is one.
-/
import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Place.placeOfPoint_degree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open scoped Classical

universe u

namespace Work.KeyLemma.Place

/-- The composite of the canonical morphism `Spec κ(x) ⟶ C` attached to a point `x` of a
curve with the structure morphism `C ⟶ Spec k` is the morphism on spectra of the canonical
`k`-algebra structure on the residue field `κ(x)`. -/
theorem fromSpecResidueField_comp_hom {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (x : C.left) :
    C.left.fromSpecResidueField x ≫ C.hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (C.left.residueField x))) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField C.hom x]
  rw [show (Spec (CommRingCat.of k)).fromSpecResidueField (C.hom x) =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec (CommRingCat.of k)).Γevaluation (C.hom x)) from by
    rw [Scheme.fromSpecResidueField, AlgebraicGeometry.Spec.fromSpecStalk_eq, ← Spec.map_comp]
    rfl]
  rw [← Spec.map_comp]
  rfl

/-- **A place of degree one is the image of a `k`-point.**  If `Q` is a place of `C` whose
degree (the dimension of its residue field over `k`) is one, then `Q` is the image of a
`k`-point of `C`. -/
theorem exists_point_of_degree_one {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    (Q : C.Place) (hQ : C.deg (Finsupp.single Q (1 : ℤ)) = 1) :
    ∃ p : Work.KeyLemma.Curve.Point C,
      Work.KeyLemma.Curve.placeOfPoint C p = Q := by
  -- The hypothesis says that the residue degree of `Q` is one.
  have hdeg : C.hom.residueDegree Q.point = 1 := by
    have h : (C.hom.residueDegree Q.point : ℤ) = 1 := by
      rw [← Work.CurveBasics.Curve.deg_place C Q]
      exact hQ
    exact_mod_cast h
  -- Equivalently, `κ(Q)` is one-dimensional over `k`.
  have hfin : Module.finrank k (C.left.residueField Q.point) = 1 := by
    rw [← Work.CurveBasics.Place.degree_eq_finrank Q]
    exact hdeg
  -- Hence the canonical map `k ⟶ κ(Q)` is bijective.
  have hbij : Function.Bijective (algebraMap k (C.left.residueField Q.point)) := by
    refine ⟨(algebraMap k _).injective, ?_⟩
    rw [finrank_eq_one_iff_of_nonzero' (1 : C.left.residueField Q.point) one_ne_zero] at hfin
    intro w
    obtain ⟨c, hc⟩ := hfin w
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (C.left.residueField Q.point))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  -- The `k`-point obtained by inverting the isomorphism `Spec κ(Q) ≅ Spec k`.
  let pleft : Spec (CommRingCat.of k) ⟶ C.left :=
    inv (Spec.map (CommRingCat.ofHom (algebraMap k (C.left.residueField Q.point)))) ≫
      C.left.fromSpecResidueField Q.point
  have hcomp : pleft ≫ C.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    simp only [pleft, Category.assoc]
    rw [fromSpecResidueField_comp_hom C Q.point, IsIso.inv_hom_id]
  let p : Work.KeyLemma.Curve.Point C := Over.homMk pleft (by simpa using hcomp)
  refine ⟨p, Subtype.ext ?_⟩
  -- `Spec κ(Q)` is a single point, so `p` lands at `Q.point`.
  show (Work.KeyLemma.Curve.Pt.leftHom p (IsLocalRing.closedPoint k)) = Q.point
  show pleft (IsLocalRing.closedPoint k) = Q.point
  simp only [pleft]
  exact Scheme.fromSpecResidueField_apply Q.point _

end Work.KeyLemma.Place
