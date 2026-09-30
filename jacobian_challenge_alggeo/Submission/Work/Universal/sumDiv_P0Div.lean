/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sum of `f` over the base divisor `P0Div` is the origin

Area UP of the Jacobian drive (`Submission/Work/Universal/Basic.lean`): for a pointed morphism
`f : C ⟶ A` of `K`-schemes into a commutative group object (`P0 ≫ f = 1`) and any field `F`
over `K`, the sum of `f` over the base divisor `P0Div` (base changed to `F`) is the origin of
`A(F)`.

The proof is the `n = 1` case of the defining property of the sum morphism `Σᵐ f`
(`sumMap`): the point of `Sym¹ C` classified by the degree-one effective divisor `P0Div`
is the image of the base point `P0` under `curveIso : C ⟶ Sym¹ C`
(`Input.P0Div_ptDiv`, `Input.curveIso_divOf`), and `Σ¹ f` transported along `curveIso` is
`f`.

The mathematical content is entirely contained in `sumMap_powMap_aux` below (the `n`-fold sum
morphism `Σⁿ f` is the sum `Σ_m f(x_m)` on `n` points of `C`), which is proved from the
defining property of `sumMap` (`sumMap_spec`) and the naturality of `powMap`
(`SymGeom.powMap_comp`).
-/
import Mathlib
import Submission.Work.Universal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

universe u v

namespace Work.Universal

noncomputable section

open Work.GCBasics Work.GroupChunk

variable {K : Type u} [Field K]

/-- **The sum morphism `Σᵐ f` evaluated on `n` points of `C`.**  For a family
`x : Fin n → (T ⟶ C)` of points of `C` parametrised by a `K`-scheme `T`, the composite of the
`n`-fold sum `powMap x : T ⟶ Symⁿ C` with `Σᵐ f` is the sum `∏ m, (x m ≫ f)` in the group
`Hom(T, A)`.

This is the `n`-fold generalisation of `curveIso_sumMap`; it is proved from `sumMap_spec`
(which identifies `quotMap ≫ Σᵐ f` with `∏ m, (pr_m ≫ f)`) together with the naturality of
`powMap` (`SymGeom.powMap_comp`) and the fact that `powMap x = Pi.lift x ≫ quotMap`. -/
theorem sumMap_powMap_aux {C : CurveBasics.Curve K}
    {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    (D : GroupChunk.Input C P0) [SymQuotData C P0 D]
    {A : Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ)
    {T : Sch K} (x : Fin n → (T ⟶ C.toOver)) :
    (D.symGeom n).powMap x ≫ sumMap D f n = ∏ m, (x m ≫ f) := by
  let g : T ⟶ SymQuot.prod C.toOver n := Limits.Pi.lift x
  have hg : ∀ m : Fin n, g ≫ proj C n m = x m := fun m => Limits.Pi.lift_comp_π x m
  have hgx : (fun m : Fin n => g ≫ proj C n m) = x := funext hg
  have h2 : (D.symGeom n).powMap x = g ≫ quotMap D n := by
    have h := SpecLin.SymGeom.powMap_comp (self := D.symGeom n) (g := g)
      (x := fun m => proj C n m)
    have hq : (D.symGeom n).powMap (fun m => proj C n m) = quotMap D n := rfl
    rw [hq, hgx] at h
    exact h
  rw [h2, Category.assoc, sumMap_spec, sumTerm, comp_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← Category.assoc, hg m]

/--
**The sum of `f` over the base divisor `P0Div` is the origin.**

For a pointed morphism `f : C ⟶ A` into a commutative group object, the sum `Σ f(P0Div)` of
`f` over the base divisor `P0Div` (base changed to any field `F` over `K`) is the origin
`zeroPt A F` of the group `A(F)`.

Indeed `bcKF F P0Div` is the degree-one effective divisor of the base point
(`Input.P0Div_ptDiv`), and the sum of a degree-one divisor `[x]` is the value `f(x)` of `f` at
`x` (`sumMap_powMap_aux` at `n = 1`, together with the fact that the point of `Sym¹ C` with
divisor `[x]` is `x ≫ curveIso`). -/
theorem sumDiv_P0Div {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] [U : Work.Universal.Input C P0]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A)
    (hf : CategoryTheory.CategoryStruct.comp P0 f = CategoryTheory.MonObj.one (X := A))
    {F : Type _} [Field F] [Algebra K F] :
    Work.Universal.sumDiv D f (Work.GroupChunk.bcKF F D.P0Div)
      (Work.Universal.bcKF_isEffective D) 1 (Work.Universal.bcKF_P0Div_deg D)
      = Work.Universal.zeroPt A F := by
  have hdiv : (D.symGeom 1).divOf ((D.symGeom 1).powMap (fun _ : Fin 1 => P0Pt C P0 F))
      = GroupChunk.bcKF F D.P0Div := by
    rw [SpecLin.SymGeom.divOf_powMap (self := D.symGeom 1)
      (x := fun _ : Fin 1 => P0Pt C P0 F)]
    rw [Fin.sum_univ_one]
    exact U.P0Div_ptDiv
  rw [sumDiv_eq_of_divOf D f (bcKF_isEffective D) (bcKF_P0Div_deg D) hdiv]
  rw [sumMap_powMap_aux D f 1 (fun _ : Fin 1 => P0Pt C P0 F)]
  rw [Fin.prod_univ_one]
  rw [P0Pt, Category.assoc, hf, zeroPt]

end

end Work.Universal
