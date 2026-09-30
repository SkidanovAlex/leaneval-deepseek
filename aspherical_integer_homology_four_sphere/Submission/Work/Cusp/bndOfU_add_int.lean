import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `bndOfU` is `1`-periodic: shifting the perimeter parameter `u` by an integer does not change
the point of `∂Sq`, because `bndOfU u` depends only on the fractional part `Int.fract u`. -/
theorem bndOfU_add_int (t : ℝ) (m : ℤ) : bndOfU (t + m) = bndOfU t := by
  unfold bndOfU
  rw [Int.fract_add_intCast]

end Work.Cusp
