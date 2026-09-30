/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose
-/
import Mathlib
import Submission.Work.CurveFacts.AddCompat
import Submission.Work.Universal.sumMap_powMap
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.Universal.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The additivity datum `Work.CurveFacts.IsAddSumMap` is a theorem

`Work.CurveFacts.addMap_divOf` -- the only compatibility that the chart datum
`Work.GroupChunk.Input` records between the addition of symmetric powers `D.addMap` and the
point/divisor dictionary `divOf` -- pins `D.addMap` at *field points*: the divisor of the sum of
two points `p`, `q` is the sum of their divisors.  Since `divOf` is injective (field point
`SymGeom.divOf_injective`) and, at a field point, a point of a symmetric power is a `powMap`
whenever its divisor splits (`SymGeom.split`, applied over an algebraic closure), it follows that
`D.addMap` is computed by `Fin.append` on field points.

Combining this with `Work.Universal.sumMap_powMap` -- which computes `sumMap D f k` at a `powMap`
*at any field point*, and which is proved for an arbitrary chart datum `D` from
`SymQuotData.desc` alone -- gives the identity

  `(lift p q ≫ D.addMap m n) ≫ sumMap D f (m+n) = (p ≫ sumMap D f m) * (q ≫ sumMap D f n)`

for all field points `p`, `q`: the datum `Work.CurveFacts.IsAddSumMap D f m n`.  This is the
hypothesis `hadd` of `Work.CurveFacts.kl_add_of_input` (area KL's additivity of `Σ f`), so that
additivity now holds for every chart datum, with no extra hypothesis.

The argument is the base-change-to-the-algebraic-closure argument of
`Work.CurveFacts.isAddSumMap_of_isAddSumMapPow`, with one difference: at the (necessarily
`powMap`-shaped) field points of the algebraic closure no `powMap`-level datum
(`Work.CurveFacts.IsAddSumMapPow`, a statement about *all* parameter schemes `T`) is needed --
the point-level computation of the sum morphism `Work.Universal.sumMap_powMap` is enough.
-/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj

universe u

namespace Work.JacClose

open Work.GCBasics

/-- **The addition of symmetric powers at a field point is `Fin.append`.**  For an arbitrary
chart datum `D`, a field `F` over `K` and points `x : Fin m → C.F`, `y : Fin n → C.F`,

`lift (powMap x) (powMap y) ≫ D.addMap m n = D.powMap (Fin.append x y)`.

This is the point-level half of `Work.SymQuot.addMap_spec` (which is available only for the
concrete symmetric powers), and it *is* a consequence of the chart datum axioms: both sides have
the same divisor (`D.addMap_divOf` on the left, `SymGeom.divOf_powMap` and
`Fin.sum_univ_add`/`Fin.append_left`/`Fin.append_right` on the right), and `divOf` is injective
(`SymGeom.divOf_injective`). -/
theorem lift_addMap_powMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) (m n : ℕ) {F : Type u} [Field F] [Algebra K F]
    (x : Fin m → Work.SpecLin.CurveFPt C F) (y : Fin n → Work.SpecLin.CurveFPt C F) :
    CategoryTheory.CartesianMonoidalCategory.lift ((D.symGeom m).powMap x)
        ((D.symGeom n).powMap y) ≫ D.addMap m n
      = (D.symGeom (m + n)).powMap (Fin.append x y) := by
  classical
  apply (D.symGeom (m + n)).divOf_injective
  let q0 : Work.GCBasics.FPt (Work.GCBasics.specOf K F) F := 𝟙 (Work.GCBasics.specOf K F)
  have h := D.addMap_divOf m n ((D.symGeom m).powMap x) ((D.symGeom n).powMap y) q0
  simp only [q0, Category.id_comp, CategoryTheory.CartesianMonoidalCategory.liftEquiv_apply] at h
  rw [h, (D.symGeom m).divOf_powMap x, (D.symGeom n).divOf_powMap y,
    (D.symGeom (m + n)).divOf_powMap (Fin.append x y), Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- **The additivity datum `Work.CurveFacts.IsAddSumMap` holds for every chart datum.**

For a chart datum `D : Work.GroupChunk.Input C P0` (with the quotient property
`Work.Universal.SymQuotData`, i.e. area SY's `desc`), a commutative group object `A` and a
morphism `f : C ⟶ A`, the sum morphism `Σ^{m+n} f : Sym^{m+n} C ⟶ A` of the sum of two points is
the product of the sums: `Work.CurveFacts.IsAddSumMap D f m n`.

Hence the hypothesis `hadd` of `Work.CurveFacts.kl_add_of_input` (the additivity of `Σ f`, area
KL) is a theorem.

Proof.  Given field points `p : FPt (Sym^m C) F`, `q : FPt (Sym^n C) F`, base change to the
algebraic closure `L = F̄` of `F` along `e : F →ₐ[K] L`: `smap_injective e` reduces the identity
to the identity after base change (`Work.GroupChunk.smap_injective`).  Over `L` the effective
divisors `divOf p`, `divOf q` split into points `x : Fin m → CurveFPt C L`,
`y : Fin n → CurveFPt C L` (`SymGeom.split`, using `SymGeom.divOf_map`), so that
`RPt.map e p = powMap x` and `RPt.map e q = powMap y` by `SymGeom.divOf_powMap` and
`SymGeom.divOf_injective`.  The left hand side is then
`lift (powMap x) (powMap y) ≫ D.addMap m n ≫ sumMap D f (m+n)`, which by
`Work.JacClose.lift_addMap_powMap` is `powMap (Fin.append x y) ≫ sumMap D f (m+n)`, and both
sides evaluate to the product `∏ r, (Fin.append x y r ≫ f)` by `Work.Universal.sumMap_powMap`
(which computes `sumMap` at a `powMap` for every parameter scheme) and
`Fin.prod_univ_add`/`Fin.append_left`/`Fin.append_right`. -/
theorem isAddSumMapOfInput {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) (m n : ℕ) :
    Work.CurveFacts.IsAddSumMap D f m n := by
  intro F _ _ p q
  -- Pass to an algebraic closure `L` of `F`, so that the divisors split into points.
  let L := AlgebraicClosure F
  let e : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  refine Work.GroupChunk.smap_injective (X := A) e _ _ ?_
  have hL : Work.GCBasics.RPt.map e
        ((CategoryTheory.CartesianMonoidalCategory.lift p q ≫ D.addMap m n)
          ≫ Work.Universal.sumMap D f (m + n))
      = (CategoryTheory.CartesianMonoidalCategory.lift (Work.GCBasics.RPt.map e p)
            (Work.GCBasics.RPt.map e q) ≫ D.addMap m n)
          ≫ Work.Universal.sumMap D f (m + n) := by
    simp only [Work.GCBasics.RPt.map]
    rw [← Category.assoc, ← Category.assoc,
      CategoryTheory.CartesianMonoidalCategory.comp_lift]
  have hR : Work.GCBasics.RPt.map e
        ((p ≫ Work.Universal.sumMap D f m) * (q ≫ Work.Universal.sumMap D f n))
      = (Work.GCBasics.RPt.map e p ≫ Work.Universal.sumMap D f m)
          * (Work.GCBasics.RPt.map e q ≫ Work.Universal.sumMap D f n) := by
    simp only [Work.GCBasics.RPt.map]
    rw [CategoryTheory.MonObj.comp_mul]
    simp only [Category.assoc]
  rw [hL, hR]
  -- Split the base changed points into points of `C` over `L`.
  obtain ⟨x, hx⟩ := (D.symGeom m).split (F := F) (F' := L)
      ((D.symGeom m).divOf p) ((D.symGeom m).divOf_isEffective p) ((D.symGeom m).divOf_deg p)
  obtain ⟨y, hy⟩ := (D.symGeom n).split (F := F) (F' := L)
      ((D.symGeom n).divOf q) ((D.symGeom n).divOf_isEffective q) ((D.symGeom n).divOf_deg q)
  have hp' : Work.GCBasics.RPt.map e p = (D.symGeom m).powMap x := by
    apply (D.symGeom m).divOf_injective
    rw [show (D.symGeom m).divOf (Work.GCBasics.RPt.map e p)
          = Work.SpecLin.DivBase.bc e ((D.symGeom m).divOf p) from
        (D.symGeom m).divOf_map e p,
      hx, (D.symGeom m).divOf_powMap x]
  have hq' : Work.GCBasics.RPt.map e q = (D.symGeom n).powMap y := by
    apply (D.symGeom n).divOf_injective
    rw [show (D.symGeom n).divOf (Work.GCBasics.RPt.map e q)
          = Work.SpecLin.DivBase.bc e ((D.symGeom n).divOf q) from
        (D.symGeom n).divOf_map e q,
      hy, (D.symGeom n).divOf_powMap y]
  rw [hp', hq']
  -- `D.addMap` is `Fin.append` at these points, and `sumMap` is the product of the `f`-images.
  rw [lift_addMap_powMap D m n x y]
  rw [Work.Universal.sumMap_powMap, Work.Universal.sumMap_powMap, Work.Universal.sumMap_powMap]
  simp only [Work.Universal.prodHom]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

end Work.JacClose
