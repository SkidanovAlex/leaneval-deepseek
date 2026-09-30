import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- For a point `P` of the upper sheet, the height coordinate of its upper half space position is
positive. -/
theorem uhsOfHyp_three_pos {P : V5} (hP : P ∈ upperSheet) : 0 < (uhsOfHyp P) 3 := by
  rw [uhsOfHyp_apply_three]
  exact inv_pos.mpr (upperSheet_four_sub_three_pos hP)

end Work.HypModel
