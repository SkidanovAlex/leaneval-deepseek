/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B3)

# Area BNChart, B3 — the Brill–Noether criterion for a concrete curve

The Brill–Noether chart `D(δ) ⊆ Sym^g C` is cut out by the determinant
`δ = det (s_j(x_m))²` of the evaluation matrix of a basis of `L(W)` at the points of a
degree-`g` divisor.  The chart works because of the criterion

  `det (s_j(x_m)) ≠ 0 ↔ i (divOf p) = 0`  (`p` a point of `C^g` landing in `U^g`),

which in the form stated by area `CH` (`Work.Charts.nonempty_BNData_of_basis`) is **false**: two
equal columns make the determinant vanish, while `i` may well be `0`.

This file assembles the two *true* directions of the criterion into the two statements that the
chart of a concrete curve actually needs:

* `Work.BNChart.iOf_eq_zero_of_det_ne_zero` — the true direction, for an *arbitrary* point of
  `C^g` landing in `U^g` (no distinctness of the points is needed);
* `Work.BNChart.exists_det_ne_zero` — the existence of a point of `C^g` landing in `U^g` whose
  evaluation matrix is invertible (built from a non-special degree-`g` divisor with *reduced*
  support in `U`, where the converse direction of the criterion does hold).

Everything is reduced to the sections `Work.BNChart.chartSection C h j` and the one bridge
`Work.BNChart.EvalSectionBridge C` between the sections on `C` and the base-changed functions on
`C_F`.
-/
import Submission.Work.BNChart.Chart
import Submission.Work.BNChart.evalSection_eq_evalAt
import Submission.Work.BNChart.iOf_eq_zero_of_det_ne_zero_point
import Submission.Work.BNChart.det_ne_zero_of_iOf_eq_zero
import Submission.Work.BNChart.exists_reduced_nonspecial_chart
import Submission.Work.Charts.Step3Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-- **The bridge `EvalSectionBridge C`**, from its explicit form
`Work.BNChart.evalSection_eq_evalAt`. -/
theorem evalSectionBridge (C : Curve K) : EvalSectionBridge C :=
  fun {F} _ _ {n} hn x h U hU hxU c hf hreg =>
    evalSection_eq_evalAt hn x h U hU hxU c hf hreg

/-- **B3, the true direction of the Brill–Noether criterion.**

If the evaluation matrix `(s_j(x_m))` of a point `p` of `C^g` landing in `U^g` is invertible, then
`i (divOf (quotMap p)) = 0`.  No distinctness of the points is needed. -/
theorem iOf_eq_zero_of_det_ne_zero {C : Curve K} [SymQuot.CurveAffineCover C]
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Cprod C (rochDataPos C h).g) F)
    (hp : RPt.LandsIn p (cgOpen C (chartU C) (rochDataPos C h).g))
    (hdet : (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left (coord_landsIn hp m)
      (chartSection C h j)))) ≠ 0) :
    iOf C (rochW C)
      (SpecLin.SymGeom.divOf (ptComp p (quotMap C (rochDataPos C h).g))) = 0 := by
  have hdiv : SpecLin.SymGeom.divOf (ptComp p (quotMap C (rochDataPos C h).g))
      = ∑ m, SpecLin.ptDiv (coord p m) := by
    rw [ptComp_apply]
    exact divOf_quotMap p
  rw [hdiv]
  exact iOf_eq_zero_of_det_ne_zero_point h (evalSectionBridge C) (fun m => coord p m)
    (fun m => coord_landsIn hp m) hdet

/-- **B3, the existence of a point of `C^g` with invertible evaluation matrix.**

Start from a non-special degree-`g` divisor `D` with *reduced* support in `U`, over the
algebraic closure of `K` (`exists_reduced_nonspecial_chart`); its support gives a point of `C^g`
landing in `U^g`, and for pairwise distinct points the converse direction of the criterion
(`det_ne_zero_of_iOf_eq_zero`) is available. -/
theorem exists_det_ne_zero {C : Curve K} [SymQuot.CurveAffineCover C]
    (h : RiemannRoch.Curve.genus C ≠ 0) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C (rochDataPos C h).g) F)
      (hp : RPt.LandsIn p (cgOpen C (chartU C) (rochDataPos C h).g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left (coord_landsIn hp m)
        (chartSection C h j)))) ≠ 0 := by
  obtain ⟨F, hF, hAlg, x, hinj, hxU, hi⟩ := exists_reduced_nonspecial_chart C h
  letI := hF
  letI := hAlg
  let p : FPt (Cprod C (rochDataPos C h).g) F :=
    Limits.Pi.lift (f := fun _ : Fin ((RiemannRoch.Curve.genus C - 1) + 1) => C.toOver) x
  have hp_eq : p = Limits.Pi.lift (f :=
      fun _ : Fin ((RiemannRoch.Curve.genus C - 1) + 1) => C.toOver) x := rfl
  have hcoord : ∀ m, coord p m = x m := by
    intro m
    show p ≫ Work.SymQuot.proj C.toOver (rochDataPos C h).g m = x m
    rw [hp_eq]
    exact Limits.Pi.lift_comp_π (f :=
      fun _ : Fin ((RiemannRoch.Curve.genus C - 1) + 1) => C.toOver) x m
  have hp : RPt.LandsIn p (cgOpen C (chartU C) (rochDataPos C h).g) := by
    change p.left (IsLocalRing.closedPoint F) ∈ cgOpen C (chartU C) (rochDataPos C h).g
    rw [mem_cgOpen]
    intro m
    show (coord p m).left (IsLocalRing.closedPoint F) ∈ chartU C
    rw [hcoord m]
    exact hxU m
  exact ⟨F, hF, hAlg, p, hp, by
    have hinj' : Function.Injective (fun m => SpecLin.ptPlace (coord p m)) := by
      intro m n hmn
      exact hinj (by simpa only [hcoord] using hmn)
    refine det_ne_zero_of_iOf_eq_zero h (evalSectionBridge C) (fun m => coord p m) hinj'
      (fun m => coord_landsIn hp m) ?_
    have hsum : (∑ m : Fin (rochDataPos C h).g, SpecLin.ptDiv (coord p m))
        = (∑ m : Fin (rochDataPos C h).g, SpecLin.ptDiv (x m)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hcoord m]
    exact (congrArg (fun D => iOf C (rochW C) D) hsum).trans hi⟩

end

end Work.BNChart
