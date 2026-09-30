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

/-- The perimeter lift `uS c p = c + frac (u p − c)` takes its values in the half-open interval
`[c, c+1)`: this is exactly the defining property of `Int.fract`, which lies in `[0,1)`, shifted
by the cut `c`. -/
theorem uS_mem (c : ℝ) (p : E2) : uS c p ∈ Set.Ico c (c + 1) := by
  rw [uS, Set.mem_Ico]
  constructor <;> linarith [Int.fract_nonneg (u p - c), Int.fract_lt_one (u p - c)]

end Work.Cusp
