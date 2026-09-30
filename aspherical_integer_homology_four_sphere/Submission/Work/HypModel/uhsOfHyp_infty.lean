import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The ideal point `∞ = (0,0,0,1,1)` is the point at infinity of the upper half space model:
its coordinate difference `∞₄ − ∞₃ = 1 − 1 = 0` vanishes, so the inverse projection `uhsOfHyp`
sends it to the "point at height `∞`" represented by the zero of `E4`. -/
theorem uhsOfHyp_infty : uhsOfHyp infty = 0 := by
  simp [uhsOfHyp, infty]

end Work.HypModel
