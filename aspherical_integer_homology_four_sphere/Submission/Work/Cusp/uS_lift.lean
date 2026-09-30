import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The shifted lift `uS c` differs from the unshifted perimeter parameter `u` by an integer.

`uS c p = c + Int.fract (u p - c) = c + ((u p - c) - ⌊u p - c⌋) = u p - ⌊u p - c⌋`,
so the integer is `m = -⌊u p - c⌋`. -/
theorem uS_lift (c : ℝ) (p : E2) : ∃ m : ℤ, uS c p = u p + m := by
  refine ⟨-⌊u p - c⌋, ?_⟩
  have h := Int.floor_add_fract (u p - c)
  simp only [uS] at *
  push_cast
  linarith

end Work.Cusp
