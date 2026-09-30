import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- For a point `q` of the upper half space chart (`0 < q 3`), the last coordinate of the lift
`hypOfUHS q = (q/s, (‖q‖²−1)/(2s), (‖q‖²+1)/(2s))` is positive: it equals `(‖q‖²+1)/(2q 3)`, a
quotient of two positive numbers. -/
theorem hypOfUHS_four_pos {q : E4} (hq : 0 < q 3) : 0 < hypOfUHS q 4 := by
  rw [hypOfUHS_apply_four]
  positivity

end Work.HypModel
