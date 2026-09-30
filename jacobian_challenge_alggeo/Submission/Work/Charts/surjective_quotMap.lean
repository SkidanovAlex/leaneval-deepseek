/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map `C^n ⟶ Sym^n C` is surjective on points

`Work.Charts.quotMap C n : C^n ⟶ Sym^n C` is the sum map `(x_m) ↦ Σ_m [x_m]` of area `SY`'s
symmetric power.  This file proves that it is surjective on the level of the underlying
topological spaces: **every point of `Sym^n C` is the sum of `n` points of `C`**.

The proof uses only the interface `Work.SpecLin.SymGeom` (area `SY`), not any property of a
particular model of `Sym^n C`:

* take a point `y` of `Sym^n C` and the canonical field point `q = resPt (Sym^n C) y` at `y`
  (`Work.GCBasics.resPt`), whose divisor `divOf q` is an effective divisor of degree `n` on
  `C_{κ(y)}`;
* split it over the algebraic closure `Ω = AlgebraicClosure (resField (Sym^n C) y)` of the
  residue field (`SymGeom.split`), obtaining `x : Fin n → C(Ω)` with `divOf q` pulled back
  `= Σ_m [x_m]`;
* the point `ξ = Pi.lift x : Ω ⟶ C^n` of the product with coordinates the `x_m` therefore
  satisfies `quotMap ξ = powMap x` (`powMap_comp`) and
  `divOf (powMap x) = Σ_m [x_m] = divOf (q_Ω)`, so `powMap x = q_Ω` by injectivity of `divOf`
  (`divOf_injective`, `divOf_map`);
* evaluating at the closed point of `Spec Ω` exhibits `y` as the image of the point
  `ξ (closedPoint Ω)` of `C^n`.

Compare `Submission/Work/Charts/ChartCg.lean`: the Brill–Noether chart is cut out of `Sym^g C`
by `δ`, and the description of its points as images of points of `C^g` goes through exactly
this surjectivity.
-/
import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

noncomputable section

/-- **The quotient map `C^n ⟶ Sym^n C` is surjective on points**: every point of `Sym^n C` is
the sum of `n` points of `C` (over the residue field of the point, split over its algebraic
closure).

This is proved from the interface `Work.SpecLin.SymGeom` alone: the point `y` is the image of
the canonical `κ(y)`-point `resPt (Sym^n C) y`, whose divisor is an effective divisor of degree
`n`, which splits over the algebraic closure into `n` points of `C`; the corresponding point of
`C^n` is the required preimage. -/
theorem surjective_quotMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (n : ℕ) [Work.SpecLin.SymGeom C n] :
    Function.Surjective (Work.Charts.quotMap C n).left.base := by
  intro y
  -- the sum `Sym^n C` and the canonical field point `q` at `y`
  let S : Work.GCBasics.Sch K := Work.Charts.Sym C n
  set q : Work.GCBasics.FPt S (Work.GCBasics.resField S y) := Work.GCBasics.resPt S y with hq
  -- its divisor is effective of degree `n`, so it splits over the algebraic closure `Ω` of the
  -- residue field `κ(y)`
  obtain ⟨x, hx⟩ := Work.SpecLin.SymGeom.split (C := C) (n := n)
    (F := Work.GCBasics.resField S y)
    (F' := AlgebraicClosure (Work.GCBasics.resField S y))
    (D := Work.SpecLin.SymGeom.divOf q)
    (Work.SpecLin.SymGeom.divOf_isEffective q) (Work.SpecLin.SymGeom.divOf_deg q)
  -- the point `ξ ∈ C^n(Ω)` with coordinates the `x m`
  let ξ : Work.GCBasics.FPt (Work.Charts.Cprod C n)
      (AlgebraicClosure (Work.GCBasics.resField S y)) :=
    Limits.Pi.lift (f := fun _ : Fin n => C.toOver) x
  have hcoord : ∀ m, Work.Charts.coord ξ m = x m := fun m =>
    Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) x m
  -- `quotMap ξ = powMap x`, by naturality of `powMap` in the parameter scheme
  have h3 : Work.SpecLin.SymGeom.powMap x = ξ ≫ Work.Charts.quotMap C n := by
    rw [show x = (fun m => ξ ≫ Work.SymQuot.proj C.toOver n m) from
      funext (fun m => (hcoord m).symm)]
    exact Work.SpecLin.SymGeom.powMap_comp (T := Work.Charts.Cprod C n) ξ
      (fun m => Work.SymQuot.proj C.toOver n m)
  -- ... and `powMap x = q_Ω`, because both have divisor `Σ_m [x_m]`
  have h2 : Work.SpecLin.SymGeom.powMap x =
      Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K (Work.GCBasics.resField S y)
          (AlgebraicClosure (Work.GCBasics.resField S y))) q := by
    apply Work.SpecLin.SymGeom.divOf_injective
    rw [Work.SpecLin.SymGeom.divOf_powMap, Work.SpecLin.SymGeom.divOf_map, ← hx]
  have hξ : ξ ≫ Work.Charts.quotMap C n =
      Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K (Work.GCBasics.resField S y)
          (AlgebraicClosure (Work.GCBasics.resField S y))) q := h3.symm.trans h2
  -- evaluate at the closed point of `Spec Ω`: `ξ (closedPoint Ω)` is the required preimage
  let u : ↥(AlgebraicGeometry.Spec (CommRingCat.of
      (AlgebraicClosure (Work.GCBasics.resField S y)))) :=
    IsLocalRing.closedPoint (AlgebraicClosure (Work.GCBasics.resField S y))
  refine ⟨(Over.Hom.left ξ) u, ?_⟩
  calc (Over.Hom.left (Work.Charts.quotMap C n)) ((Over.Hom.left ξ) u)
      = (Over.Hom.left ξ ≫ Over.Hom.left (Work.Charts.quotMap C n)) u :=
        (Scheme.Hom.comp_apply (Over.Hom.left ξ)
          (Over.Hom.left (Work.Charts.quotMap C n)) u).symm
    _ = (Over.Hom.left (ξ ≫ Work.Charts.quotMap C n)) u := by rw [Over.comp_left]
    _ = (Over.Hom.left (Work.SpecLin.RPt.map
          (IsScalarTower.toAlgHom K (Work.GCBasics.resField S y)
            (AlgebraicClosure (Work.GCBasics.resField S y))) q)) u := by rw [hξ]
    _ = y := by
        rw [show Work.SpecLin.RPt.map
            (IsScalarTower.toAlgHom K (Work.GCBasics.resField S y)
              (AlgebraicClosure (Work.GCBasics.resField S y))) q =
            Work.SpecLin.specOfMap (K := K)
              (IsScalarTower.toAlgHom K (Work.GCBasics.resField S y)
                (AlgebraicClosure (Work.GCBasics.resField S y))) ≫ q from rfl]
        rw [Over.comp_left, Scheme.Hom.comp_apply, hq]
        exact Work.GCBasics.resPt_apply S y _

end

end Work.Charts
