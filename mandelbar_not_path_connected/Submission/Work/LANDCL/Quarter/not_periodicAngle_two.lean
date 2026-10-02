import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The parameter angle `23/63` is not of period `2`

`Work.Landing.paramAngle = 23/63` is periodic of period `6` under angle doubling
`angDouble θ = fract (-2θ)`, with orbit `23/63 → 17/63 → 29/63 → 5/63 → 53/63 → 20/63 → 23/63`.
In particular its second iterate is `29/63 ≠ 23/63`, so `2` is not a period of `paramAngle`.

The statement is a specialisation of the exact-period computation
`Work.Landing.Angle.exactPeriodAngle_paramAngle` (which imports through
`Submission.Work.LANDCL.Defs`).
-/

namespace Work.LANDCL.Quarter

theorem not_periodicAngle_two :
    ¬ Work.Landing.PeriodicAngle Work.Landing.paramAngle 2 :=
  fun h => Work.Landing.Angle.exactPeriodAngle_paramAngle.2.2 2 (by norm_num) (by norm_num) h

end Work.LANDCL.Quarter
