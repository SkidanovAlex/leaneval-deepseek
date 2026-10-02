import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- `wakeArc` is periodic with period `5` in its index: it is defined by matching on `j % 5`. -/
theorem wakeArc_eq_of_mod_eq {j k : ℕ} (h : j % 5 = k % 5) :
    Work.Landing.wakeArc j = Work.Landing.wakeArc k := by
  simp only [Work.Landing.wakeArc, h]

/-- Moving one step in the index of `wakeArc` shifts the residue `j % 5` by one (mod `5`). -/
theorem wakeArc_succ_mod (j : ℕ) : (j + 1) % 5 = (j % 5 + 1) % 5 := by omega

/-- The lifted arcs are successive images: doubling sends the two ends of `wakeArc j` to the two
ends of `wakeArc (j+1)` (modulo `1`, since the lifted representatives exceed `1`), exchanging them. -/
theorem wakeArc_step (j : ℕ) :
    Int.fract (-2 * (Work.Landing.wakeArc j).1) = Int.fract (Work.Landing.wakeArc (j + 1)).2 ∧
      Int.fract (-2 * (Work.Landing.wakeArc j).2) = Int.fract (Work.Landing.wakeArc (j + 1)).1 := by
  have hlt : j % 5 < 5 := Nat.mod_lt j (by norm_num)
  have hmod : (j + 1) % 5 = (j % 5 + 1) % 5 := wakeArc_succ_mod j
  interval_cases hj : j % 5 <;>
    simp only [Work.Landing.wakeArc, hmod, hj] <;> norm_num [Int.fract]

end Work.Landing.Angle
