import Mathlib
import Submission.Work.KeyLemma.Pencil
import Submission.Work.AbVar.Main
import Submission.Work.AbVar.P1Chart.Geom
import Submission.Work.AbVar.P1Chart.isDomain_tensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-!
# The pencil rational map `C ⇢ ℙ¹` attached to a rational function

For a curve `C` over a field `k` and a rational function `h ∈ K(C)`, this file constructs the
rational map `[h : 1] : C ⇢ ℙ¹_k` (the "pencil map" of `h`), the chart ring map `k[t] → K(C)`
sending the coordinate `t` to `h`, and the identification of the generic fibre.

This is the first ingredient of the geometric input `Curve.PencilGeometric` of the key lemma
over an algebraically closed field (see `Submission/Work/KeyLemma/NOTES.md`, Addendum 3).
-/
namespace Work.KeyLemma.Curve

open Work.CurveBasics

universe u

variable {k : Type u} [Field k]

/-- The `k`-algebra isomorphism between the `i`-th standard chart ring `AX k i` of `ℙ¹` and the
polynomial ring in the chart coordinate `t = X_{other}/X_i`. -/
noncomputable def chartEquiv (k : Type u) [Field k] :
    Polynomial ↥(Work.AbVar.P1Chart.gr k 0) ≃ₐ[↥(Work.AbVar.P1Chart.gr k 0)]
      Work.AbVar.P1Chart.AX k 1 :=
  AlgEquiv.ofBijective
    (Polynomial.aeval (Work.AbVar.P1Chart.t k 1) :
      Polynomial ↥(Work.AbVar.P1Chart.gr k 0) →ₐ[↥(Work.AbVar.P1Chart.gr k 0)]
        Work.AbVar.P1Chart.AX k 1)
    ⟨Work.AbVar.P1Chart.aeval_t_inj k 1, Work.AbVar.P1Chart.aeval_t_surj k 1⟩

/-- The chart coordinate of `AX k 1` is the polynomial variable. -/
lemma chartEquiv_X (k : Type u) [Field k] :
    (chartEquiv k) Polynomial.X = Work.AbVar.P1Chart.t k 1 := by
  have h : (chartEquiv k) Polynomial.X
      = (Polynomial.aeval (Work.AbVar.P1Chart.t k 1) :
          Polynomial ↥(Work.AbVar.P1Chart.gr k 0) →ₐ[↥(Work.AbVar.P1Chart.gr k 0)]
            Work.AbVar.P1Chart.AX k 1) Polynomial.X := rfl
  rw [h, Polynomial.aeval_X]

/-- The constants of the chart ring. -/
lemma chartEquiv_C (k : Type u) [Field k] (a : ↥(Work.AbVar.P1Chart.gr k 0)) :
    (chartEquiv k) (Polynomial.C a) = algebraMap ↥(Work.AbVar.P1Chart.gr k 0)
      (Work.AbVar.P1Chart.AX k 1) a := by
  have h : (chartEquiv k) (Polynomial.C a)
      = (Polynomial.aeval (Work.AbVar.P1Chart.t k 1) :
          Polynomial ↥(Work.AbVar.P1Chart.gr k 0) →ₐ[↥(Work.AbVar.P1Chart.gr k 0)]
            Work.AbVar.P1Chart.AX k 1) (Polynomial.C a) := rfl
  rw [h, Polynomial.aeval_C]

/-- **The function on the chart of `ℙ¹` induced by a rational function**, on the chart `X₁ ≠ 0`
where the coordinate is `t = X₀/X₁`: the `k`-algebra map `k[t] ≅ AX k 1 → K(C)` sending `t` to
`h`.  This is the restriction to the chart of the rational map `C ⇢ ℙ¹` given by `[h : 1]`. -/
noncomputable def chartRingHom (C : Curve k) (h : C.functionField) :
    Work.AbVar.P1Chart.AX k 1 →+* C.functionField :=
  RingHom.comp (Polynomial.aeval h).toRingHom
    (RingHom.comp (Polynomial.mapRingHom (Work.AbVar.p1BaseEquiv k).symm.toRingHom)
      (chartEquiv k).symm.toRingHom)

/-- The chart-ring map sends the coordinate `t` to `h`. -/
lemma chartRingHom_t (C : Curve k) (h : C.functionField) :
    chartRingHom C h (Work.AbVar.P1Chart.t k 1) = h := by
  have ht : (chartEquiv k).symm (Work.AbVar.P1Chart.t k 1) = Polynomial.X := by
    rw [← chartEquiv_X k, AlgEquiv.symm_apply_apply]
  have h2 : (chartEquiv k).symm.toRingHom (Work.AbVar.P1Chart.t k 1) = Polynomial.X := ht
  simp only [chartRingHom, RingHom.comp_apply, h2]
  simp

/-- The chart-ring map sends constants to the corresponding constants of `K(C)`. -/
lemma chartRingHom_const (C : Curve k) (h : C.functionField)
    (a : ↥(Work.AbVar.P1Chart.gr k 0)) :
    chartRingHom C h (algebraMap ↥(Work.AbVar.P1Chart.gr k 0)
      (Work.AbVar.P1Chart.AX k 1) a)
      = algebraMap k C.functionField ((Work.AbVar.p1BaseEquiv k).symm a) := by
  have h2 : (chartEquiv k).symm.toRingHom (algebraMap ↥(Work.AbVar.P1Chart.gr k 0)
      (Work.AbVar.P1Chart.AX k 1) a) = Polynomial.C a := by
    change (chartEquiv k).symm (algebraMap _ _ a) = Polynomial.C a
    rw [AlgEquiv.symm_apply_eq, chartEquiv_C]
  simp only [chartRingHom, RingHom.comp_apply, h2, Polynomial.coe_mapRingHom, Polynomial.map_C]
  show (Polynomial.aeval h) (Polynomial.C ((Work.AbVar.p1BaseEquiv k).symm.toRingHom a))
      = algebraMap k C.functionField ((Work.AbVar.p1BaseEquiv k).symm a)
  rw [Polynomial.aeval_C]
  rfl

/-- The morphism `Spec K(C) ⟶ ℙ¹` given by the chart coordinate `h` (the point `[h : 1]`). -/
noncomputable def toProj (C : Curve k) (h : C.functionField) :
    Spec (CommRingCat.of C.functionField) ⟶ AlgebraicGeometry.Proj (Work.AbVar.P1Grading k) :=
  Spec.map (CommRingCat.ofHom (chartRingHom C h)) ≫
    Proj.awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
      (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos

/-- `Spec K(C) ⟶ ℙ¹` is a morphism over `Spec k` (for the canonical `k`-algebra structure on
`K(C)`). -/
lemma toProj_base (C : Curve k) (h : C.functionField) :
    toProj C h ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) := by
  rw [Work.AbVar.p1_hom, toProj]
  simp only [Category.assoc]
  rw [← Category.assoc (Proj.awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
        (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos) (Proj.toSpecZero (Work.AbVar.P1Grading k))
        (Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom))]
  rw [Proj.awayι_toSpecZero (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
      (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply]
  change chartRingHom C h (algebraMap ↥(Work.AbVar.P1Chart.gr k 0)
      (Work.AbVar.P1Chart.AX k 1) (Work.AbVar.p1BaseEquiv k a)) = algebraMap k C.functionField a
  rw [chartRingHom_const, RingEquiv.symm_apply_apply]

/-- The same morphism, as a point of `ℙ¹` over the function field of `C`, in the form needed by
`Scheme.RationalMap.ofFunctionField`. -/
lemma toProj_base' (C : Curve k) (h : C.functionField) :
    toProj C h ≫ (Work.AbVar.P1 k).hom
      = C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom := by
  rw [toProj_base, ← Work.CurveBasics.fromSpecStalk_genericPoint_comp_hom]

/-- The morphism `Spec K(C) ⟶ ℙ¹` as an element of the over-category. -/
noncomputable def specKToP1 (C : Curve k) (h : C.functionField) :
    Over.mk (C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom) ⟶ Work.AbVar.P1 k :=
  Over.homMk (toProj C h) (toProj_base' C h)

/-- **The rational map `C ⇢ ℙ¹` attached to a rational function `h`** (the map `[h : 1]`), as a
rational map over `Spec k`. -/
noncomputable def pencilRatMap (C : Curve k) (h : C.functionField) :
    C.toOver.left ⤏ (Work.AbVar.P1 k).left := by
  haveI : Smooth (Work.AbVar.P1 k).hom := Work.AbVar.ProjectiveLine.smooth
  haveI : LocallyOfFiniteType (Work.AbVar.P1 k).hom := inferInstance
  exact Scheme.RationalMap.ofFunctionField C.toOver.hom (Work.AbVar.P1 k).hom
    (specKToP1 C h).left (specKToP1 C h).w

/-- The generic fibre of the pencil rational map is `[h : 1]`. -/
lemma pencilRatMap_fromFunctionField (C : Curve k) (h : C.functionField) :
    (pencilRatMap C h).fromFunctionField = (specKToP1 C h).left := by
  haveI : Smooth (Work.AbVar.P1 k).hom := Work.AbVar.ProjectiveLine.smooth
  haveI : LocallyOfFiniteType (Work.AbVar.P1 k).hom := inferInstance
  exact Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _

end Work.KeyLemma.Curve

namespace Work.KeyLemma.Curve

universe u

