/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B4, §2.B6)

# Area BNChart — the Brill–Noether chart and COV′ for a concrete curve

This is the assembly of the area: from the Riemann–Roch data of `Basic` (B1), the chart data and
the base-changed basis of `Chart` (B2), the two true directions of the Brill–Noether criterion of
`Criterion` (B3) and the RESID data of `Resid` (B5), it produces

* `Work.BNChart.nonempty_BNData` — **B4**: the Brill–Noether chart `BNData C (rochDataPos C h)`
  of a concrete curve exists;
* `Work.BNChart.exists_galCharts` — **B6**: COV′ over `k`, i.e. the Galois-equivariant covering
  `GalCharts C (rochDataPos C h) P0` of `Pic⁰` by translates of that chart (over a finite Galois
  extension), which is what area `DS`/`JacClose` consumes.

The only hypothesis of `exists_galCharts` beyond the curve and the base point is the integral
closedness of the local rings of `Sym^{g+g} C` (`hstalk`), which is area `CurveFacts`' A4; it is
taken here as a hypothesis exactly as the lead's closure design prescribes.
-/
import Submission.Work.BNChart.ChartData
import Submission.Work.BNChart.BNData
import Submission.Work.BNChart.Criterion
import Submission.Work.BNChart.Resid
import Submission.Work.Charts.Step3Main
import Submission.Work.SymQuot.SymProps

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

/-- **B4: the Brill–Noether chart of a concrete curve exists.**

The chart is built by `Work.BNChart.nonempty_BNData_of_hcrit` on the affine open `chartU C` of
`C` avoiding the support of the canonical divisor, with the sections `chartSection C h` of the
canonical basis, the auxiliary place `chartQ C`, the basis `chartH` of `(C_K).L (rochW C)`:

* the true direction of the criterion is `Work.BNChart.iOf_eq_zero_of_det_ne_zero`;
* the existence of a point with invertible evaluation matrix is
  `Work.BNChart.exists_det_ne_zero`;
* the invariance of `ℓ` under base change is `Work.BNChart.ell_bc`. -/
theorem nonempty_BNData (C : Curve K) [SymQuot.CurveAffineCover C]
    (h : RiemannRoch.Curve.genus C ≠ 0) :
    Nonempty (BNData C (rochDataPos C h)) :=
  nonempty_BNData_of_hcrit (rochDataPos C h) (chartU C) (isAffineOpen_chartU C) (chartQ C)
    (fun j => ((chartH C h j : (C.baseChange K).L (rochW C))
      : (C.baseChange K).functionField))
    (chartH_mem C h) (span_chartH C h) (chartSection C h)
    (fun p hp hdet => iOf_eq_zero_of_det_ne_zero h p hp hdet)
    (exists_det_ne_zero h) (fun e D => ell_bc e D)

/-- **B6: COV′ over the base field.**

`Work.Charts.exists_galCharts_of_inputs` fed with the Riemann–Roch data `rochDataPos C h` (B1),
the Brill–Noether chart (B4), the RESID data `residData C _` (B5), the geometry of the symmetric
powers (`Work.Charts.instSymProps`) and the normality hypothesis `hstalk` (area `CurveFacts` A4).

The symmetric powers are the concrete family `SymQuot.symGeomFamily C`; only the values at
`(rochDataPos C h).g` and at `(rochDataPos C h).g + (rochDataPos C h).g` are used, and both are
successors, so the `match` in `symGeomFamily` reduces definitionally. -/
theorem exists_galCharts (C : Curve K) [SymQuot.CurveAffineCover C]
    (h : RiemannRoch.Curve.genus C ≠ 0)
    (P0 : unitSch K ⟶ C.toOver)
    (hstalk : ∀ x : ((SymQuot.symGeomFamily C
        ((rochDataPos C h).g + (rochDataPos C h).g)).S).left,
      IsIntegrallyClosed (((SymQuot.symGeomFamily C
        ((rochDataPos C h).g + (rochDataPos C h).g)).S).left.presheaf.stalk x)) :
    Nonempty (@GalCharts K _ C _ (rochDataPos C h)
      (SymQuot.symGeomFamily C (rochDataPos C h).g) P0) := by
  letI : SpecLin.SymGeom C (rochDataPos C h).g := SymQuot.symGeomFamily C (rochDataPos C h).g
  refine Work.Charts.exists_galCharts_of_inputs (rochDataPos C h) (SymQuot.symGeomFamily C)
    (residData C (rochDataPos C h)) ?_ ?_ hstalk P0
    (Classical.choice (nonempty_BNData C h))
  · exact Work.Charts.instSymProps C (rochDataPos C h).g
  · exact Work.Charts.instSymProps C ((rochDataPos C h).g + (rochDataPos C h).g)

end

end Work.BNChart
