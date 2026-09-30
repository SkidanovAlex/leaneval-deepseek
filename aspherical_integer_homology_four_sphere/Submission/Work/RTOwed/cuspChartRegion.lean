/-
# The cusp chart on its region: the non-junk branch of `mbarLow`

`cuspLowPt` (and hence `mbarLow`) is defined with a junk branch; this file shows that on the region
of interest (heights in `[s1, the ceiling of the cube]`) the branch is never taken, so `mbarLow`
is the `mk` of an explicit chart value there.  It is the form in which the fields of
`Work.Cusp.CuspGlueData` are proved.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.chartKlein_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix
open Set Topology Function

namespace Work.RTOwed

/-- **The value of the cusp chart in the region**: for heights above `s1` and below the ceiling of
the cube containing `q`, the chart is the (non-junk) branch of `cuspLowPt`. -/
theorem mbarLow_eq (v : Fin 5) {q : CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ ceilH (chartCube v q) (chartRed v q)) :
    mbarLow v q = Work.FoldInst.mk (cubeBit (chartCube v q),
      ⟨redChart v (chartCube v q) q,
        chartKlein_mem (chartCube v q) (redV_mem_cubeBox v (uhsXj q)) hs1 hs2⟩) := by
  have h : redChart v (cubeOf v (uhsXj q)) q ∈ Work.FoldInst.Qbar :=
    chartKlein_mem (cubeOf v (uhsXj q)) (redV_mem_cubeBox v (uhsXj q)) hs1 hs2
  show Work.FoldInst.mk (cuspLowPt v q) = _
  rw [cuspLowPt, dif_pos h]
  rfl


end Work.RTOwed
