import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Place.placeOfPoint_degree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `toDiv` is injective

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k`.  A multiset of
`k`-points of `C` (`Work.KeyLemma.Curve.SumDiv C`) gives rise to an effective divisor
`∑_p s p · [placeOfPoint C p]` (`Work.KeyLemma.Curve.SumDiv.toDiv C s`), and this file shows
that this construction loses no information: `toDiv C` is injective.

The mathematical input is that a `k`-point of `C` is determined by its image point: the image of
a `k`-point is a closed point `Q` of `C` of degree one
(`Work.KeyLemma.Place.placeOfPoint_degree`), hence with residue field `k`; a morphism
`Spec k ⟶ C` with image point `Q` is determined by the induced map
`𝒪_{C,Q} ⟶ k` (`Scheme.SpecToEquivOfLocalRing`), and any two such local maps agree because the
structure map `k ⟶ 𝒪_{C,Q}` is a section of them and has, after passing to residue fields,
image `k` (`residueFieldMap_surjective_of_point`).  The formal proof of that statement is
`placeOfPoint_injective_aux` below.

The main result of this file is `Work.KeyLemma.Sum.toDiv_injective`.

## Main results

* `Work.KeyLemma.Sum.placeOfPoint_injective_aux`
* `Work.KeyLemma.Sum.toDiv_injective`
-/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped Classical

set_option linter.style.haveILetI false

namespace Work.KeyLemma.Sum

variable {k : Type u} [Field k]

/-- The unique point of `Spec k`, for `k` a field. -/
abbrev curvePointClosedPoint (k : Type u) [Field k] : Spec (CommRingCat.of k) :=
  IsLocalRing.closedPoint k

/-- The residue field map at the image point of a `k`-point of a curve is surjective.

The residue degree of the image place of a `k`-point is one
(`Work.KeyLemma.Place.placeOfPoint_degree`), so the structure map
`κ(C.hom x) ⟶ κ(x)` of residue fields is a surjection. -/
theorem residueFieldMap_surjective_of_point (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) :
    Function.Surjective
      (C.hom.residueFieldMap ((Work.KeyLemma.Curve.Pt.leftHom p)
        (curvePointClosedPoint k))).hom := by
  have hdeg : C.hom.residueDegree
      ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k)) = 1 :=
    Work.KeyLemma.Place.placeOfPoint_degree C p
  letI : Algebra
      ((Spec (CommRingCat.of k)).residueField
        (C.hom ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))))
      (C.left.residueField ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))) :=
    (C.hom.residueFieldMap ((Work.KeyLemma.Curve.Pt.leftHom p)
      (curvePointClosedPoint k))).hom.toAlgebra
  have hfin : Module.finrank
      ((Spec (CommRingCat.of k)).residueField
        (C.hom ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))))
      (C.left.residueField ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))) = 1 := by
    rw [Scheme.Hom.residueDegree] at hdeg
    exact hdeg
  have htop : (⊥ : Subalgebra
      ((Spec (CommRingCat.of k)).residueField
        (C.hom ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))))
      (C.left.residueField ((Work.KeyLemma.Curve.Pt.leftHom p)
        (curvePointClosedPoint k)))) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hfin
  intro y
  have hy : y ∈ (⊥ : Subalgebra
      ((Spec (CommRingCat.of k)).residueField
        (C.hom ((Work.KeyLemma.Curve.Pt.leftHom p) (curvePointClosedPoint k))))
      (C.left.residueField ((Work.KeyLemma.Curve.Pt.leftHom p)
        (curvePointClosedPoint k)))) := by
    rw [htop]; trivial
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hy
  refine ⟨c, ?_⟩
  rw [RingHom.algebraMap_toAlgebra] at hc
  exact hc

set_option maxHeartbeats 1000000 in
/-- Two `k`-points of a curve with the same image point are equal.

Both morphisms `Spec k ⟶ C` are sections of the structure morphism of `C`, so their composites
with `C.hom` are equal; comparing the induced pairs of `Scheme.SpecToEquivOfField` at the level
of `Spec k` shows that the induced maps of residue fields `κ(x) ⟶ k` differ by the canonical
isomorphism `κ(f z) ≅ κ(g z)`, and the surjectivity of the structure map on residue fields
(`residueFieldMap_surjective_of_point`) upgrades this to the equality of the induced maps, whence
the two points agree by `Scheme.SpecToEquivOfField`. -/
theorem placeOfPoint_injective_aux (C : Work.CurveBasics.Curve k) :
    Function.Injective (Work.KeyLemma.Curve.placeOfPoint C) := by
  intro p q hpq
  have hx : Work.KeyLemma.Curve.Pt.leftHom p (curvePointClosedPoint k)
      = Work.KeyLemma.Curve.Pt.leftHom q (curvePointClosedPoint k) :=
    congrArg Subtype.val hpq
  have hcomp : Work.KeyLemma.Curve.Pt.leftHom p ≫ C.hom
      = Work.KeyLemma.Curve.Pt.leftHom q ≫ C.hom := by
    rw [Work.KeyLemma.Curve.Pt.leftHom_comp p, Work.KeyLemma.Curve.Pt.leftHom_comp q]
  have hpair := congrArg ((Spec (CommRingCat.of k)).SpecToEquivOfField k) hcomp
  obtain ⟨e₀, h₀⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hpair
  have e : (Work.KeyLemma.Curve.Pt.leftHom p ≫ C.hom) (curvePointClosedPoint k)
      = (Work.KeyLemma.Curve.Pt.leftHom q ≫ C.hom) (curvePointClosedPoint k) := e₀
  have h : Scheme.descResidueField (Scheme.stalkClosedPointTo
        (Work.KeyLemma.Curve.Pt.leftHom p ≫ C.hom))
      = ((Spec (CommRingCat.of k)).residueFieldCongr e).hom
        ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo
            (Work.KeyLemma.Curve.Pt.leftHom q ≫ C.hom)) := h₀
  rw [Scheme.descResidueField_stalkClosedPointTo_comp C.hom,
      Scheme.descResidueField_stalkClosedPointTo_comp C.hom] at h
  have hcg : (Spec (CommRingCat.of k)).residueFieldCongr e
      = (Spec (CommRingCat.of k)).residueFieldCongr
          (congrArg C.hom hx : C.hom (Work.KeyLemma.Curve.Pt.leftHom p
              (curvePointClosedPoint k))
            = C.hom (Work.KeyLemma.Curve.Pt.leftHom q (curvePointClosedPoint k))) := by
    rw [show e = (congrArg C.hom hx : C.hom (Work.KeyLemma.Curve.Pt.leftHom p
            (curvePointClosedPoint k))
            = C.hom (Work.KeyLemma.Curve.Pt.leftHom q (curvePointClosedPoint k))) from
      Subsingleton.elim _ _]
  rw [hcg] at h
  rw [CommRingCat.hom_ext_iff] at h
  have hsurj := residueFieldMap_surjective_of_point C p
  have h2 := Scheme.Hom.residueFieldMap_congr' (f := C.hom) hx
  have hpt : ∀ (c : (Spec (CommRingCat.of k)).residueField
        (C.hom (Work.KeyLemma.Curve.Pt.leftHom p (curvePointClosedPoint k)))),
      (Scheme.descResidueField (Scheme.stalkClosedPointTo (Work.KeyLemma.Curve.Pt.leftHom p)))
        ((C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom p
          (curvePointClosedPoint k))) c)
      = (Scheme.descResidueField (Scheme.stalkClosedPointTo (Work.KeyLemma.Curve.Pt.leftHom q)))
        ((C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom q (curvePointClosedPoint k)))
          (((Spec (CommRingCat.of k)).residueFieldCongr (congrArg C.hom hx)).hom c)) := by
    intro c
    exact DFunLike.congr_fun h c
  have h2pt : ∀ (c : (Spec (CommRingCat.of k)).residueField
        (C.hom (Work.KeyLemma.Curve.Pt.leftHom p (curvePointClosedPoint k)))),
      (C.left.residueFieldCongr hx).hom
          ((C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom p
            (curvePointClosedPoint k))) c)
      = (C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom q (curvePointClosedPoint k)))
          (((Spec (CommRingCat.of k)).residueFieldCongr (congrArg C.hom hx)).hom c) := by
    intro c
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) c
  have hψ : Scheme.descResidueField (Scheme.stalkClosedPointTo (Work.KeyLemma.Curve.Pt.leftHom p))
      = (C.left.residueFieldCongr hx).hom
        ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo
            (Work.KeyLemma.Curve.Pt.leftHom q)) := by
    rw [CommRingCat.hom_ext_iff]
    refine RingHom.ext (fun y => ?_)
    obtain ⟨c, hc⟩ := hsurj y
    rw [← hc]
    show (Scheme.descResidueField (Scheme.stalkClosedPointTo (Work.KeyLemma.Curve.Pt.leftHom p)))
        ((C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom p
          (curvePointClosedPoint k))) c)
      = (Scheme.descResidueField (Scheme.stalkClosedPointTo (Work.KeyLemma.Curve.Pt.leftHom q)))
        ((C.left.residueFieldCongr hx).hom
          ((C.hom.residueFieldMap (Work.KeyLemma.Curve.Pt.leftHom p
            (curvePointClosedPoint k))) c))
    rw [hpt c]
    congr 1
    exact (h2pt c).symm
  have hpairs : C.left.SpecToEquivOfField k (Work.KeyLemma.Curve.Pt.leftHom p)
      = C.left.SpecToEquivOfField k (Work.KeyLemma.Curve.Pt.leftHom q) := by
    rw [Scheme.SpecToEquivOfField_eq_iff]
    exact ⟨hx, hψ⟩
  exact Over.OverMorphism.ext ((C.left.SpecToEquivOfField k).injective hpairs)

/-- The divisor `toDiv C s` of a multiset of points is the image of `s` under
`Finsupp.mapDomain (placeOfPoint C)` followed by the inclusion `ℕ ↪ ℤ`. -/
theorem toDiv_eq_mapDomain (C : Work.CurveBasics.Curve k)
    (s : Work.KeyLemma.Curve.SumDiv C) :
    Work.KeyLemma.Curve.SumDiv.toDiv C s
      = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
          (Finsupp.mapDomain (Work.KeyLemma.Curve.placeOfPoint C) s) := by
  ext Q
  rw [Work.KeyLemma.Curve.SumDiv.toDiv_apply, Work.KeyLemma.Curve.SumDiv.coeffAt,
    Finsupp.mapRange_apply, Finsupp.mapDomain_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum, Finsupp.sum]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by split <;> simp

theorem toDiv_injective {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) :
    Function.Injective (Work.KeyLemma.Curve.SumDiv.toDiv C) := by
  have hinj : Function.Injective (Work.KeyLemma.Curve.placeOfPoint C) :=
    placeOfPoint_injective_aux C
  intro s t hst
  have h1 : Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
        (Finsupp.mapDomain (Work.KeyLemma.Curve.placeOfPoint C) s)
      = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
        (Finsupp.mapDomain (Work.KeyLemma.Curve.placeOfPoint C) t) := by
    rw [← toDiv_eq_mapDomain C s, ← toDiv_eq_mapDomain C t, hst]
  exact Finsupp.mapDomain_injective hinj
    (Finsupp.mapRange_injective _ _ (fun _ _ hab => Nat.cast_injective hab) h1)

end Work.KeyLemma.Sum
