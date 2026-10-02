import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- The angle-doubling map on `ℝ` and the angle-doubling map on `ℚ` agree on rational
angles, and hence so do all their iterates: for `q : ℚ`, the `n`-th iterate of
`angDouble` at `q` is the cast to `ℝ` of the `n`-th iterate of `angDoubleQ` at `q`.

This is the iterate-level form of `angDouble_coe_rat`; it is used to transfer
computations of periodic orbits of rational angles from `ℚ` (where they are exact
arithmetic) to `ℝ` (where the dynamics lives). -/
theorem angDouble_coe_rat_iterate (q : ℚ) (n : ℕ) :
    (Work.Landing.angDouble)^[n] (q : ℝ) = (((Work.Landing.angDoubleQ)^[n] q : ℚ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [Work.Landing.angDouble, Work.Landing.angDoubleQ]
    rw [show (-2 : ℝ) * (((Work.Landing.angDoubleQ)^[n] q : ℚ) : ℝ) =
          (((-2 : ℚ) * (Work.Landing.angDoubleQ)^[n] q : ℚ) : ℝ) by push_cast; ring]
    exact (Rat.cast_fract ((-2 : ℚ) * (Work.Landing.angDoubleQ)^[n] q)).symm

end Work.Landing.Angle
