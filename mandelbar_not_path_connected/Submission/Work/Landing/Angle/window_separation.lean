import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- The two windows `rootAngle1 ± windowEps` and `rootAngle2 ± windowEps` around the dynamic
root angles of the non-real period-`5` component are disjoint and separated by the parameter
angle `paramAngle = 23/63`: both windows lie inside `(0,1)` and the interval between them
contains `paramAngle`. -/
theorem window_separation :
    0 < Work.Landing.rootAngle1 - Work.Landing.windowEps ∧
    Work.Landing.rootAngle1 + Work.Landing.windowEps < Work.Landing.paramAngle ∧
    Work.Landing.paramAngle < Work.Landing.rootAngle2 - Work.Landing.windowEps ∧
    Work.Landing.rootAngle2 + Work.Landing.windowEps < 1 := by
  unfold Work.Landing.rootAngle1 Work.Landing.rootAngle2 Work.Landing.paramAngle
    Work.Landing.windowEps
  norm_num

end Work.Landing.Angle
