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

/-- Shifting the argument of the fractional part: `frac (c + frac (x − c)) = frac x`.  Indeed the
two arguments differ by the integer `⌊x − c⌋`, by `Int.fract_add_floor`. -/
lemma fract_add_fract_sub (c x : ℝ) : Int.fract (c + Int.fract (x - c)) = Int.fract x := by
  rw [Int.fract_eq_fract]
  refine ⟨-⌊x - c⌋, ?_⟩
  rw [← Int.self_sub_floor]
  push_cast
  ring

/-- The fractional part of the shifted perimeter lift `uS c` is the fractional part of `u`:
`uS c p = c + frac (u p − c)` differs from `u p` by an integer. -/
theorem fract_uS (c : ℝ) (p : E2) : Int.fract (uS c p) = Int.fract (u p) := by
  rw [uS, fract_add_fract_sub]

end Work.Cusp
