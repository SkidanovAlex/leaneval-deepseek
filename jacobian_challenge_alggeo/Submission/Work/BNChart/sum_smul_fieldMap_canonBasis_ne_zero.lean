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

/-- A nonzero `F`-linear combination of the base-changed basis elements
`fieldMap (canonBasis C h j)` is nonzero, since these elements are linearly independent. -/
theorem sum_smul_fieldMap_canonBasis_ne_zero {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (c : Work.BNChart.chartIdx C → F) (hc : c ≠ 0) :
    (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
        ((Work.BNChart.canonBasis C h j : C.L (RiemannRoch.Curve.canonical C))
          : C.functionField)) ≠ 0 := by
  intro h0
  have hLI := linearIndependent_fieldMap_canonBasis C h F
  rw [Fintype.linearIndependent_iff] at hLI
  exact hc (funext (hLI c h0))

end Work.BNChart
