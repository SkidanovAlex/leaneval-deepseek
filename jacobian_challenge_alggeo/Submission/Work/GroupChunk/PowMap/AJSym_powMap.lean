/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — `AJSym` is the `g`-fold sum of `AJ₀`

The Abel–Jacobi morphism `AJSym : Sym^g C ⟶ G D` of `Submission/Work/GroupChunk/AJSym.lean`
is constructed (in `AJSym_exists.lean`) by gluing the local RESID chart maps, and is therefore
only characterised by its class map: `D.cls (p ≫ D.AJSym) = D.picAJ p` at every field point
(`Input.cls_AJSym`).  This file proves the missing *morphism-level* description of `AJSym`,
namely that it is the `g`-fold sum of the Abel–Jacobi map `AJ₀ : C ⟶ G D`:

`(D.symGeom D.g).powMap x ≫ D.AJSym = ∏ m, (x m ≫ AJ₀)`,

for an arbitrary family of `g` points `x m : T ⟶ C` parametrised by a `K`-scheme `T`.

The product on the right is taken in the (commutative) group of morphisms
`Hom(T, G D)`; its commutativity is the Mathlib theorem
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` (a proper,
geometrically integral group scheme over a field is commutative), which is why the hypotheses
`IsProper` and `GeometricallyIntegral` appear in the statement.

## The proof

* `cls_prod_finset`: the class map `D.cls` is multiplicative, so the class of a point composed
  with a finite product of morphisms into `G D` is the sum of the classes.  This is where the
  hypothesis `hmul` (the class map is additive with respect to the group law `μ`) is used.
* `picAJ_powMap`: at a field point, the class `picAJ` of the `g`-fold sum of `g` points of `C`
  is the sum of the classes `cls (x m ≫ AJ₀) = [x m] - [P0]`.  This is a computation in the
  abelian group `Pic⁰(C_F)`, using `SymGeom.divOf_powMap` (`divOf (powMap x) = Σ ptDiv (x m)`)
  and `AJ.cls_AJ0`.
* `symGeom_powMap_proj_AJSym`: the *universal* case `T = C^g` with `x m` the `m`-th projection.
  Two morphisms out of the reduced scheme `C^g` into the separated scheme `G D` which have the
  same class at every field point are equal (`GroupLaw.hom_ext_cls_pt`); reducedness of the
  power `C^g` is `SymQuot.Prod.isReduced_pi_prod`.
* `AJSym_powMap`: the general case follows from the universal one by precomposing with
  `Pi.lift x : T ⟶ C^g`, using the naturality of `powMap` in the parameter scheme and the
  compatibility of finite products of morphisms with precomposition.
-/
import Mathlib
import Submission.Work.GroupChunk.Interface
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Glue
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.AJ0Basic
import Submission.Work.GroupChunk.Assembly
import Submission.Work.GroupChunk.GroupLaw.grpObj_exists
import Submission.Work.GroupChunk.AJ.cls_AJ0
import Submission.Work.AbVar.Basic
import Submission.Work.SymQuot.All
import Submission.Work.SymQuot.Prod.isReduced_pi_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory AlgebraicGeometry
open Work.GCBasics

universe u

namespace Work.GroupChunk.PowMap

noncomputable section

variable {K : Type u} [Field K] {C : CurveBasics.Curve K}
  {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

/-! ## Finite products of morphisms into a monoid object -/

/-- A morphism distributes over a finite product of morphisms into a commutative monoid
object: `g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, (g ≫ u i)`. -/
theorem comp_prod_finset {M : Sch K} [MonObj M] [IsCommMonObj M] {X Y : Sch K} {β : Type*}
    (s : Finset β) (g : X ⟶ Y) (u : β → (Y ⟶ M)) :
    g ≫ (∏ i ∈ s, u i) = ∏ i ∈ s, (g ≫ u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

/-- A finite product of morphisms into a commutative monoid object is compatible with
precomposition. -/
theorem prod_of_comp {β : Type*} [Fintype β] {T Y : Sch K} (L : T ⟶ Y)
    {M : Sch K} [MonObj M] [IsCommMonObj M] (u : β → (Y ⟶ M)) (w : β → (T ⟶ M))
    (hw : ∀ i, L ≫ u i = w i) : L ≫ (∏ i, u i) = ∏ i, w i := by
  rw [comp_prod_finset (Finset.univ : Finset β) L u]
  exact Finset.prod_congr rfl (fun i _ => hw i)

/-! ## The class map of the group chunk -/

/-- The unit of the group of `F`-points of `G D` has class zero: this follows from the
additivity `hmul` of the class map, applied to the unit. -/
theorem cls_one_point (D : Input C P0) [GrpObj (GSch D)]
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt (GSch D) F),
      D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ μ[GSch D]) = D.cls p + D.cls q)
    {F : Type u} [Field F] [Algebra K F] :
    D.cls (1 : FPt (GSch D) F) = 0 := by
  have hkey : CartesianMonoidalCategory.liftEquiv
        ((1 : FPt (GSch D) F), (1 : FPt (GSch D) F))
        ≫ μ[GSch D] = (1 : FPt (GSch D) F) := by
    rw [CartesianMonoidalCategory.liftEquiv_apply, ← Hom.mul_def, mul_one]
  have hm := hmul (p := (1 : FPt (GSch D) F)) (q := 1)
  rw [hkey] at hm
  have hm' : D.cls (1 : FPt (GSch D) F) + 0
      = D.cls (1 : FPt (GSch D) F) + D.cls (1 : FPt (GSch D) F) := by
    rw [add_zero]; exact hm
  exact (add_left_cancel hm').symm

/-- **The class of a point composed with a finite product** of morphisms into the group chunk
is the sum of the classes of the factors. -/
theorem cls_prod_finset (D : Input C P0) [GrpObj (GSch D)]
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt (GSch D) F),
      D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ μ[GSch D]) = D.cls p + D.cls q)
    {Y : Sch K} {F : Type u} [Field F] [Algebra K F] (p : FPt Y F) {β : Type*}
    (s : Finset β) (u : β → (Y ⟶ GSch D)) :
    D.cls (p ≫ ∏ i ∈ s, u i) = ∑ i ∈ s, D.cls (p ≫ u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, MonObj.comp_one]
      exact cls_one_point D hmul
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h : D.cls (p ≫ (u a * ∏ i ∈ s, u i))
          = D.cls (p ≫ u a) + D.cls (p ≫ ∏ i ∈ s, u i) := by
        rw [MonObj.comp_mul p (u a) (∏ i ∈ s, u i), Hom.mul_def]
        exact hmul (p := p ≫ u a) (q := p ≫ ∏ i ∈ s, u i)
      rw [h, ih]

/-! ## Sums of classes in `Pic⁰` -/

/-- In the subgroup `div0 C F ⊆ Div(C_F)` of divisors of degree zero, a finite sum is computed
on the underlying divisors. -/
theorem div0_sum {F : Type u} [Field F] [Algebra K F] {β : Type*} (a : β → Dv C F)
    (ha : ∀ i, Ddeg C F (a i) = 0) (s : Finset β) :
    (∑ i ∈ s, (⟨a i, ha i⟩ : div0 C F))
      = ⟨∑ i ∈ s, a i, by
          show Ddeg C F (∑ i ∈ s, a i) = 0
          rw [map_sum]
          exact Finset.sum_eq_zero (fun i _ => ha i)⟩ := by
  apply Subtype.ext
  have h := map_sum (div0 C F).subtype (fun i => (⟨a i, ha i⟩ : div0 C F)) s
  simpa using h

/-- A finite sum of classes in `Pic⁰` of divisors of degree zero is the class of the sum of the
divisors. -/
theorem Pic0_sum_mk {F : Type u} [Field F] [Algebra K F] {β : Type*} (a : β → Dv C F)
    (ha : ∀ i, Ddeg C F (a i) = 0) :
    ∀ (s : Finset β) (hs : Ddeg C F (∑ i ∈ s, a i) = 0),
      ∑ i ∈ s, Pic0.mk (a i) (ha i) = Pic0.mk (∑ i ∈ s, a i) hs := by
  intro s hs
  refine (map_sum (Pic0.mkHom C F) (fun i => (⟨a i, ha i⟩ : div0 C F)) s).symm.trans ?_
  congr 1
  exact div0_sum a ha s

/-! ## The class of the `g`-fold sum of `g` points of `C` -/

/-- **The key point-level computation**: the Abel–Jacobi class of the `g`-fold sum of `g`
points `x m` of `C` is the sum of the classes `[x m] - [P0]`, i.e. the sum of the classes of
the `g` points `x m ≫ AJ₀` of `G D`. -/
theorem picAJ_powMap (D : Input C P0) [GrpObj (GSch D)]
    {F : Type u} [Field F] [Algebra K F] (x : Fin D.g → FPt C.toOver F) :
    D.picAJ ((D.symGeom D.g).powMap x) = ∑ m, D.cls (x m ≫ D.AJ₀) := by
  have hdiv : D.divOf D.g ((D.symGeom D.g).powMap x) = ∑ m, SpecLin.ptDiv (x m) :=
    (D.symGeom D.g).divOf_powMap x
  have hbc : bcKF F D.P0g = D.g • bcKF F D.P0Div := by
    rw [Input.P0g]
    let f : Dv C K →+ Dv C F :=
      { toFun := bcKF F
        map_zero' := SpecLin.DivBase.bc_zero (Algebra.ofId K F)
        map_add' := fun A B => SpecLin.DivBase.bc_add (Algebra.ofId K F) A B }
    change f (D.g • D.P0Div) = D.g • f D.P0Div
    rw [map_nsmul]
  have hsumsub : (∑ m, (SpecLin.ptDiv (x m) - bcKF F D.P0Div))
      = (∑ m, SpecLin.ptDiv (x m)) - D.g • bcKF F D.P0Div := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h3 : Ddeg C F (∑ m, (SpecLin.ptDiv (x m) - bcKF F D.P0Div)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun m _ => Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) (x m))
  have hsum : (∑ m : Fin D.g, Ddeg C F (SpecLin.ptDiv (x m))) = (D.g : ℤ) := by
    have h : ∀ m : Fin D.g, Ddeg C F (SpecLin.ptDiv (x m)) = (1 : ℤ) :=
      fun m => SpecLin.Points.ptDiv_deg (x m)
    rw [Finset.sum_congr rfl (fun m _ => h m), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simp
  have h4 : Ddeg C F ((∑ m, SpecLin.ptDiv (x m)) - D.g • bcKF F D.P0Div) = 0 := by
    rw [map_sub, map_sum, map_nsmul, deg_bcKF F D.P0Div, Input.P0Div_deg, hsum]
    simp
  have hleft : D.picAJ ((D.symGeom D.g).powMap x)
      = Pic0.mk ((∑ m, SpecLin.ptDiv (x m)) - D.g • bcKF F D.P0Div) h4 := by
    have h1 : D.picAJ ((D.symGeom D.g).powMap x)
        = Pic0.mk (D.divOf D.g ((D.symGeom D.g).powMap x) - bcKF F D.P0g)
            (by
              have h1 : Ddeg C F (D.divOf D.g ((D.symGeom D.g).powMap x)) = (D.g : ℤ) :=
                (D.symGeom D.g).divOf_deg _
              have h2 : Ddeg C F (bcKF F D.P0g) = (D.g : ℤ) := by
                rw [deg_bcKF, Input.P0g_deg]
              rw [map_sub, h1, h2, sub_self]) := rfl
    rw [h1, Pic0.mk_eq_iff, hdiv, hbc]
    exact LinEquiv.refl _
  have hright : (∑ m, D.cls (x m ≫ D.AJ₀))
      = Pic0.mk (∑ m, (SpecLin.ptDiv (x m) - bcKF F D.P0Div)) h3 := by
    rw [show (∑ m, D.cls (x m ≫ D.AJ₀))
        = ∑ m, Pic0.mk (SpecLin.ptDiv (x m) - bcKF F D.P0Div)
            (Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) (x m)) from
      Finset.sum_congr rfl (fun m _ => AJ.cls_AJ0 D (x m))]
    exact Pic0_sum_mk (fun m => SpecLin.ptDiv (x m) - bcKF F D.P0Div)
      (fun m => Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) (x m)) Finset.univ h3
  rw [hleft, hright, Pic0.mk_eq_iff, ← hsumsub]
  exact LinEquiv.refl _

/-! ## The universal case -/

/-- **The universal case**: the Abel–Jacobi morphism composed with the `g`-fold sum of the
`g` universal points of `C^g` is the product of the `g` Abel–Jacobi images. -/
theorem symGeom_powMap_proj_AJSym (D : Input C P0) [GrpObj (GSch D)]
    [IsProper (GSch D).hom] [GeometricallyIntegral (GSch D).hom]
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt (GSch D) F),
      D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ μ[GSch D]) = D.cls p + D.cls q) :
    (D.symGeom D.g).powMap (fun m => SymQuot.proj C.toOver D.g m) ≫ D.AJSym
      = ∏ m, (SymQuot.proj C.toOver D.g m ≫ D.AJ₀) := by
  haveI : IsReduced (SymQuot.prod C.toOver D.g).left :=
    SymQuot.Prod.isReduced_pi_prod C.toOver D.g
  refine GroupLaw.hom_ext_cls_pt (D := D) (Y := SymQuot.prod C.toOver D.g) ?_
  intro F _ _ p
  rw [← Category.assoc,
    ← (D.symGeom D.g).powMap_comp p (fun m => SymQuot.proj C.toOver D.g m)]
  rw [Input.cls_AJSym D]
  rw [cls_prod_finset D hmul p Finset.univ (fun m => SymQuot.proj C.toOver D.g m ≫ D.AJ₀)]
  rw [show (∑ m, D.cls (p ≫ SymQuot.proj C.toOver D.g m ≫ D.AJ₀))
      = ∑ m, D.cls ((p ≫ SymQuot.proj C.toOver D.g m) ≫ D.AJ₀) from
    Finset.sum_congr rfl (fun m _ => by simp only [Category.assoc])]
  exact picAJ_powMap D (fun m => p ≫ SymQuot.proj C.toOver D.g m)

/-- **`AJSym` is the `g`-fold sum of `AJ₀`.**  For every family `x : Fin g → (T ⟶ C)` of `g`
points of `C` parametrised by a `K`-scheme `T`, the composite of `AJSym` with the `g`-fold sum
`powMap x` is the product of the points `x m ≫ AJ₀` in the group `Hom(T, G D)`. -/
theorem AJSym_powMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [GrpObj (Work.GroupChunk.GSch D)] [IsProper (Work.GroupChunk.GSch D).hom]
    [GeometricallyIntegral (Work.GroupChunk.GSch D).hom]
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F]
      (p q : Work.GCBasics.FPt (Work.GroupChunk.GSch D) F),
      Work.GroupChunk.Input.cls D
        (CartesianMonoidalCategory.liftEquiv (p, q) ≫ μ[Work.GroupChunk.GSch D]) =
          Work.GroupChunk.Input.cls D p + Work.GroupChunk.Input.cls D q) :
    ∀ {T : Work.GCBasics.Sch K} (x : Fin D.g → (T ⟶ C.toOver)),
      (D.symGeom D.g).powMap x ≫ D.AJSym = ∏ m, (x m ≫ Work.GroupChunk.Input.AJ₀ D) := by
  intro T x
  -- the `g`-fold sum of `x` is `x` lifted to the product of `g` copies of `C`, followed by
  -- the universal `g`-fold sum
  let L : T ⟶ SymQuot.prod C.toOver D.g := Limits.Pi.lift x
  have hL : L = Limits.Pi.lift x := rfl
  have hnat : (D.symGeom D.g).powMap x
      = L ≫ (D.symGeom D.g).powMap (fun m => SymQuot.proj C.toOver D.g m) :=
    (congrArg (fun z : Fin D.g → (T ⟶ C.toOver) => (D.symGeom D.g).powMap z)
      (funext (fun m => (Limits.Pi.lift_comp_π x m).symm))).trans
      ((D.symGeom D.g).powMap_comp (Limits.Pi.lift x)
        (fun m => SymQuot.proj C.toOver D.g m))
  rw [hnat, Category.assoc, symGeom_powMap_proj_AJSym D hmul]
  exact prod_of_comp L (fun m => SymQuot.proj C.toOver D.g m ≫ D.AJ₀) (fun m => x m ≫ D.AJ₀)
    (fun m => by rw [hL, ← Category.assoc, Limits.Pi.lift_comp_π])

end

end Work.GroupChunk.PowMap
