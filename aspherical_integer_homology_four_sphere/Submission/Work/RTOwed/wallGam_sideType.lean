import Mathlib
import Submission.Work.RTOwed.cuspChartWalls
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- On the upper face `j = 1` of the cube `a`, the wall table agrees with the fold-side type: the
copy bit of the far cube is the copy bit of `a` shifted by the flip bit, and the Klein sign change
and flip bit of the wall identification `(wallGamK, wallGamFlip)` are exactly the `sideType` of the
upper wall `wallHi a j`.  Both sides are finite tables, so the statement is a finite check. -/
theorem wallGam_sideType (a : Fin 48) (j : Fin 3) :
    Work.RTOwed.cubeBit (Work.RTOwed.wallNb a j 1)
        = Work.RTOwed.cubeBit a + Work.RTOwed.wallGamFlip a j 1 ∧
    (Work.RTOwed.wallGamK a j 1, Work.RTOwed.wallGamFlip a j 1)
        = Work.FoldInst.sideType (Work.RTOwed.wallHi a j) := by
  revert a j
  decide +kernel

end Work.RTOwed
