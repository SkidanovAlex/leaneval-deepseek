import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The parameter ray angle `23/63` has exact period `6` under angle doubling

`paramAngle = 23/63` labels the parameter ray `R(23/63)` used in the endgame of the
tricorn proof.  Its orbit under angle doubling `angDouble θ = fract (-2θ)` is

`23/63 → 17/63 → 29/63 → 5/63 → 53/63 → 20/63 → 23/63`,

so `23/63` is periodic of period `6` and of no smaller period.  The `6 ∤ 10` property this
records is what rules out landing at a parabolic point of the period-`5` orbit (whose second
return multiplier is `1`), so that `R(23/63)` lands at a repelling periodic point.

This file proves the exactness part `ExactPeriodAngle paramAngle 6` by direct rational
arithmetic: the iterate formula `angDouble^[n+1] θ = fract ((-2)^(n+1) θ)` is not needed,
because `norm_num` can evaluate `Int.fract` at a rational and unroll the finite iterate.
-/

namespace Work.Landing.Angle

/-- The angle `23/63` is periodic of period `6` under angle doubling, and no smaller positive
period works: `23/63` has **exact** period `6`. -/
theorem exactPeriodAngle_paramAngle :
    Work.Landing.ExactPeriodAngle Work.Landing.paramAngle 6 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · -- `angDouble^[6] (23/63) = fract (64 * 23/63) = fract (1472/63) = 23/63`.
    show (Work.Landing.angDouble)^[6] Work.Landing.paramAngle = Work.Landing.paramAngle
    norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
  · -- The only positive `m < 6` are `1,…,5`; for each, the iterate is a rational different
    -- from `23/63` (`17/63`, `29/63`, `5/63`, `53/63`, `20/63`), a contradiction.
    intro m hm hlt hper
    rw [Work.Landing.PeriodicAngle] at hper
    interval_cases m <;>
      norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero_apply] at hper

end Work.Landing.Angle
