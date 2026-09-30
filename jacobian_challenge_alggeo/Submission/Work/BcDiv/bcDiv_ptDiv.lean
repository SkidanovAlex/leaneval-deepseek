import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.BcDiv.Points
import Submission.Work.BcDiv.ramIdx_cmp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

noncomputable section

/-- The projection of the comparison square `bcSq : (C_L)_F ⟶ C_F` is an isomorphism (it is the
comparison of two models of the same base change). -/
theorem isIso_bcSq_π {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F] :
    IsIso (bcSq (C := C) (L := L) (F := F)).π :=
  BCSquare.instIsIso_cmp_π (sqLF (C := C) (L := L) (F := F)) (sqF (C := C) (F := F))

/-- **The sections of the two models correspond**: the section of `C_F` attached to the point
`bcPtK x` is the transport of the section of `(C_L)_F` attached to `x` along the comparison
square `bcSq`. -/
theorem ptLeft_bcPtK {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (x : Work.SpecLin.CurveFPt (C.baseChange L) F) :
    Work.SpecLin.ptLeft (bcPtK x) ≫ (bcSq (C := C) (L := L) (F := F)).π
      = Work.SpecLin.ptLeft x := by
  -- the projection `bcSq.π`, tested against the two projections of `(C_L)_F = C_L ×_L Spec F`
  have key1 : (bcSq (C := C) (L := L) (F := F)).π
      ≫ Curve.baseChangeFst (C.baseChange L) F ≫ Curve.baseChangeFst C L
      = Curve.baseChangeFst C F := by
    change (bcSq (C := C) (L := L) (F := F)).π
      ≫ (sqLF (C := C) (L := L) (F := F)).π = Curve.baseChangeFst C F
    rw [BCSquare.cmp_π_comp]
    rfl
  have key2 : (bcSq (C := C) (L := L) (F := F)).π
      ≫ Curve.baseChangeFst (C.baseChange L) F ≫ (C.baseChange L).hom
      = (C.baseChange F).hom ≫ Curve.specMap L F := by
    have h : Curve.baseChangeFst (C.baseChange L) F ≫ (C.baseChange L).hom
        = ((C.baseChange L).baseChange F).hom ≫ Curve.specMap L F := by
      rw [Curve.baseChange_hom (C.baseChange L) F]
      exact pullback.condition
    rw [h, ← Category.assoc, BCSquare.cmp_π_hom]
  -- the two composites of `bcSq.π` with the projections of `C_L = C ×_K Spec L` pin it down
  have key3 : Work.SpecLin.ptLeft (bcPtK x)
      ≫ ((bcSq (C := C) (L := L) (F := F)).π
          ≫ Curve.baseChangeFst (C.baseChange L) F) = x.left := by
    refine IsPullback.hom_ext (IsPullback.of_hasPullback C.hom (Curve.specMap K L)) ?_ ?_
    · change (Work.SpecLin.ptLeft (bcPtK x)
          ≫ ((bcSq (C := C) (L := L) (F := F)).π
              ≫ Curve.baseChangeFst (C.baseChange L) F)) ≫ Curve.baseChangeFst C L
          = x.left ≫ Curve.baseChangeFst C L
      rw [Category.assoc, Category.assoc, key1, Work.SpecLin.ptLeft_fst, bcPtK_left]
      rfl
    · change (Work.SpecLin.ptLeft (bcPtK x)
          ≫ ((bcSq (C := C) (L := L) (F := F)).π
              ≫ Curve.baseChangeFst (C.baseChange L) F)) ≫ (C.baseChange L).hom
          = x.left ≫ (C.baseChange L).hom
      rw [Category.assoc, Category.assoc, key2, ← Category.assoc,
        Work.SpecLin.Points.ptLeft_comp_hom, Category.id_comp]
      exact (Over.w x).symm
  -- now the same for `ptLeft x`
  refine IsPullback.hom_ext
    (IsPullback.of_hasPullback ((C.baseChange L).hom) (Curve.specMap L F)) ?_ ?_
  · change (Work.SpecLin.ptLeft (bcPtK x) ≫ (bcSq (C := C) (L := L) (F := F)).π)
        ≫ Curve.baseChangeFst (C.baseChange L) F
        = Work.SpecLin.ptLeft x ≫ Curve.baseChangeFst (C.baseChange L) F
    rw [Category.assoc, key3, Work.SpecLin.ptLeft_fst]
  · change (Work.SpecLin.ptLeft (bcPtK x) ≫ (bcSq (C := C) (L := L) (F := F)).π)
        ≫ ((C.baseChange L).baseChange F).hom
        = Work.SpecLin.ptLeft x ≫ ((C.baseChange L).baseChange F).hom
    rw [Category.assoc, BCSquare.cmp_π_hom, Work.SpecLin.Points.ptLeft_comp_hom,
      Work.SpecLin.Points.ptLeft_comp_hom]

/-- **The comparison square carries the closed point of `bcPtK x` to the closed point of `x`.** -/
theorem bcSq_π_ptToPoint {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (x : Work.SpecLin.CurveFPt (C.baseChange L) F) :
    (bcSq (C := C) (L := L) (F := F)).π.base
      (Work.SpecLin.ptToPoint (bcPtK x)) = Work.SpecLin.ptToPoint x := by
  rw [Work.SpecLin.ptToPoint, Work.SpecLin.ptToPoint]
  change (bcSq (C := C) (L := L) (F := F)).π
      ((Work.SpecLin.ptLeft (bcPtK x)) (IsLocalRing.closedPoint F))
    = (Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)
  rw [← Scheme.Hom.comp_apply, ptLeft_bcPtK]

/-- **The place above a place of `C_F` is the place of `bcPtK x` exactly when it is the image
of the place of `x` under the (bijective on points) comparison projection.** -/
theorem bcSq_under_eq_ptPlace_iff {K : Type u} [Field K] {C : Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (x : Work.SpecLin.CurveFPt (C.baseChange L) F) (Q' : (C.baseChange F).Place)
    (h : IsClosed ({(bcSq (C := C) (L := L) (F := F)).π Q'.point}
      : Set ((C.baseChange L).baseChange F).left)) :
    (bcSq (C := C) (L := L) (F := F)).under Q' h = Work.SpecLin.ptPlace x
      ↔ Q' = Work.SpecLin.ptPlace (bcPtK x) := by
  haveI : IsIso (bcSq (C := C) (L := L) (F := F)).π := isIso_bcSq_π (C := C) (L := L) (F := F)
  have hinj : Function.Injective (bcSq (C := C) (L := L) (F := F)).π.base :=
    (Scheme.homeoOfIso (asIso (bcSq (C := C) (L := L) (F := F)).π)).injective
  constructor
  · intro heq
    have h1 : (bcSq (C := C) (L := L) (F := F)).π Q'.point
        = Work.SpecLin.ptToPoint x := congrArg Subtype.val heq
    refine Subtype.ext (hinj ?_)
    show (bcSq (C := C) (L := L) (F := F)).π Q'.1
      = (bcSq (C := C) (L := L) (F := F)).π (Work.SpecLin.ptToPoint (bcPtK x))
    rw [bcSq_π_ptToPoint]
    exact h1
  · intro hQ'
    subst hQ'
    exact Subtype.ext (bcSq_π_ptToPoint x)

/-- **B3, point divisors.** The identification `Work.BcDiv.bcDiv` of the divisor groups of
`(C_L)_F` and `C_F` sends the divisor `[x]` of an `F`-point `x` of `C_L` to the divisor of the
corresponding `F`-point `Work.BcDiv.bcPtK x` of `C`.

Proof route (helpers to be proved inside the file):
* `bcSq` is a comparison square, so `Work.BcDiv.BCSquare.cmpIso_inv` and
  `Work.BcDiv.BCSquare.instIsIso_cmp_π` give that its projection
  `bcSq.π : C_F.left ⟶ (C_L)_F.left` is an isomorphism, and `Work.BcDiv.ramIdx_cmp` gives
  `bcSq.ramIdx Q' = 1` for every place `Q'` of `C_F`;
* the sections correspond: `ptLeft (bcPtK x) ≫ bcSq.π = ptLeft x` (obtained by
  `IsPullback.hom_ext` on the pullback `(C_L)_F = C_L ×_L Spec F`, i.e. `Work.SpecLin.ptLeft_fst`
  and `Work.SpecLin.ptLeft`'s defining property, then again `IsPullback.hom_ext` on
  `(C_L) = C ×_K Spec L` using `Work.BcDiv.BCSquare.cmp_π_comp` and `bcPtK_left`);
* conclude by `Finsupp.ext` and `Work.SpecLin.ptDiv_apply`: at a place `Q'` of `C_F`, the
  coefficient of `bcSq.divMap (ptDiv x)` is `(ptDiv x) (bcSq.under Q') * bcSq.ramIdx Q'`, which
  is `1` exactly when `Q'` is the place of `C_F` attached to `bcPtK x` (else `0`), by the
  injectivity of `bcSq.π` on points;
* `Work.BcDiv.bcDiv_apply` identifies `bcDiv` with `bcSq.divMap`.

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/bcDiv_ptDiv.lean`; imports
`Submission.Work.BcDiv.Points`, `Submission.Work.BcDiv.ramIdx_cmp`. -/
theorem bcDiv_ptDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (x : Work.SpecLin.CurveFPt (C.baseChange L) F) :
    Work.BcDiv.bcDiv (Work.SpecLin.ptDiv x) = Work.SpecLin.ptDiv (Work.BcDiv.bcPtK x) := by
  have hplace := bcSq_under_eq_ptPlace_iff (C := C) (L := L) (F := F)
  ext Q'
  rw [bcDiv_apply, Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff]
  by_cases hQ : Q' = Work.SpecLin.ptPlace (bcPtK x)
  · -- the coefficient at the place of `bcPtK x`
    subst hQ
    have hcl : IsClosed ((singleton ((bcSq (C := C) (L := L) (F := F)).π
        (Work.SpecLin.ptPlace (bcPtK x)).point))
        : Set ((C.baseChange L).baseChange F).left) := by
      show IsClosed ((singleton ((bcSq (C := C) (L := L) (F := F)).π
        (Work.SpecLin.ptToPoint (bcPtK x)))) : Set _)
      rw [bcSq_π_ptToPoint]
      exact (Work.SpecLin.ptPlace x).isClosed
    rw [dif_pos hcl]
    have hunder : (bcSq (C := C) (L := L) (F := F)).under
        (Work.SpecLin.ptPlace (bcPtK x)) hcl = Work.SpecLin.ptPlace x :=
      (hplace x _ hcl).mpr rfl
    rw [hunder, ramIdx_cmp, Work.SpecLin.ptDiv_apply, Work.SpecLin.ptDiv_apply,
      if_pos rfl, if_pos rfl]
    norm_num
  · -- every other place gets coefficient `0` on both sides
    rw [Work.SpecLin.ptDiv_apply, if_neg (fun h => hQ h.symm)]
    split_ifs with hc
    · rw [Work.SpecLin.ptDiv_apply,
        if_neg (fun h => hQ ((hplace x Q' hc).mp h.symm)), zero_mul]
    · rfl

end

end Work.BcDiv
