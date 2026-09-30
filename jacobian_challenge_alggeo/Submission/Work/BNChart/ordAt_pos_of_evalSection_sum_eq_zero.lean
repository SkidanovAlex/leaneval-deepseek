import Mathlib
import Submission.Work.BNChart.Chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.BNChart

/-- If the evaluation-matrix row combination `∑ j, c j * s_j(x m)` vanishes for every `m`, then
the function `f = ∑ j, c j • fieldMap (h_j)` on `C_F` has strictly positive order of vanishing at
each `ptPlace (x m)`.  This is the `EvalSectionBridge` applied pointwise. -/
theorem ordAt_pos_of_evalSection_sum_eq_zero {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (hbridge : Work.BNChart.EvalSectionBridge C)
    (x : Fin ((RiemannRoch.Curve.genus C - 1) + 1) → Work.SpecLin.CurveFPt C F)
    (hxU : ∀ m, (x m).left (IsLocalRing.closedPoint F) ∈ Work.BNChart.chartU C)
    (c : Work.BNChart.chartIdx C → F)
    (hf : (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
        ((Work.BNChart.canonBasis C h j
          : ↥(Work.CurveBasics.Curve.L C (RiemannRoch.Curve.canonical C))) : C.functionField)) ≠ 0)
    (hreg : ∀ m, 0 ≤ (C.baseChange F).ordAt
        (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
          ((Work.BNChart.canonBasis C h j
            : ↥(Work.CurveBasics.Curve.L C (RiemannRoch.Curve.canonical C))) : C.functionField))
        (Work.SpecLin.ptPlace (x m)))
    (hc : ∀ m, ∑ j, c j * Work.Charts.evalSection (x m).left (hxU m)
        (Work.BNChart.chartSection C h j) = 0) :
    ∀ m, 0 < (C.baseChange F).ordAt
        (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
          ((Work.BNChart.canonBasis C h j
            : ↥(Work.CurveBasics.Curve.L C (RiemannRoch.Curve.canonical C))) : C.functionField))
        (Work.SpecLin.ptPlace (x m)) := by
  intro m
  have hn : 0 < (RiemannRoch.Curve.genus C - 1) + 1 := by omega
  refine (hbridge (F := F) (n := (RiemannRoch.Curve.genus C - 1) + 1) hn (x m)
    (fun j => ((canonBasis C h j
      : C.L (RiemannRoch.Curve.canonical C)) : C.functionField))
    (chartU C) (chartU_le_regularOpens C h) (hxU m) c hf (hreg m)).mp (hc m)

end Work.BNChart
