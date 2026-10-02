import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- The width of the `j`-th lifted arc of the L-wake condition is `33·2^j / 1023`. -/
theorem wakeArc_width (j : ℕ) :
    (Work.Landing.wakeArc j).2 - (Work.Landing.wakeArc j).1 =
      33 * 2 ^ (j % 5) / 1023 := by
  have hlt : j % 5 < 5 := Nat.mod_lt j (by norm_num)
  interval_cases hj : j % 5 <;> simp only [Work.Landing.wakeArc, hj] <;> norm_num

end Work.Landing.Angle
