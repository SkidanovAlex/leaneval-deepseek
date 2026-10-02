import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

open Function

/-- The first dynamic root angle `371/1023` of the non-real period-`5` component has
exact period `10` under angle doubling `θ ↦ -2θ mod 1`.

The orbit of `371/1023` is
`371/1023 → 281/1023 → 461/1023 → 101/1023 → 821/1023 → 404/1023 →
 215/1023 → 593/1023 → 860/1023 → 326/1023 → 371/1023`,
so `angDouble^[10]` returns to `371/1023` and no smaller positive iterate does.  The fifth
iterate lands on the second dynamic root angle `angDouble^[5] rootAngle1 = rootAngle2`, i.e.
the first-return map of the period-`5` orbit exchanges the two root angles. -/
theorem exactPeriodAngle_rootAngle1 :
    Work.Landing.ExactPeriodAngle Work.Landing.rootAngle1 10 := by
  unfold Work.Landing.ExactPeriodAngle Work.Landing.PeriodicAngle
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num [Work.Landing.angDouble, Work.Landing.rootAngle1, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
  · intro m hm hm10 hper
    interval_cases m <;>
      (exfalso; revert hper;
       norm_num [Work.Landing.angDouble, Work.Landing.rootAngle1, Int.fract,
         Function.iterate_succ_apply', Function.iterate_zero_apply])

end Work.Landing.Angle
