import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- At the junction layer `t = 1/2` the exponent `2t − 1` of the ceiling `b = β(x)` vanishes while
the exponent `2 − 2t` of `s_J` becomes `1`, so the collar height is exactly the junction height
`s_J`, independently of the ceiling reached. -/
theorem collarHeight_half (b : ℝ) : collarHeight (1/2) b = sJ := by
  unfold collarHeight sJ
  norm_num

end Work.Cusp
