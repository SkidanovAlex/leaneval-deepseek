import Mathlib
import Submission.Work.Landing.Angles
import Submission.Work.Landing.Angle.wakeArc_step
import Submission.Work.Landing.Angle.angDouble_fract

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The endpoints of the lifted wake arcs

The lifted arcs `wakeArc j` of the L-wake condition (`Work.Landing.wakeArc`) are the successive
images of the root-ray pair `{371, 404}/1023` under the lifted doubling map `θ ↦ -2θ`.  This file
shows that, modulo `1`, the two endpoints of `wakeArc j` are exactly the two `j`-th iterates of the
dynamic root angles under angle doubling `angDouble θ = Int.fract (-2θ)`:

`{fract (wakeArc j).1, fract (wakeArc j).2} = {angDouble^[j] rootAngle1, angDouble^[j] rootAngle2}`.

## Proof shape

This is proved by induction on `j`, using the one-step relation `wakeArc_step`
(`{-2·(wakeArc j).1, -2·(wakeArc j).2}` reduces modulo `1` to the *reversed* pair of endpoints of
`wakeArc (j+1)`) together with `angDouble_fract` (angle doubling only depends on the angle modulo
`1`, so it may be applied to the already reduced representatives).  Since the step reverses the two
endpoints, the induction is on the *unordered* pair, which is why the statement is about sets.
-/

namespace Work.Landing.Angle

open Work.Landing Function

/-- One step of the induction: if the unordered pair `{a,b}` equals `{c,d}`, then applying
`angDouble` to both members and swapping the order of the first pair gives the same set. -/
private theorem angDouble_pair_step (a b c d : ℝ) (h : ({a, b} : Set ℝ) = {c, d}) :
    ({Work.Landing.angDouble b, Work.Landing.angDouble a} : Set ℝ)
      = {Work.Landing.angDouble c, Work.Landing.angDouble d} := by
  have h' := congrArg (Set.image Work.Landing.angDouble) h
  rw [Set.image_pair, Set.image_pair] at h'
  rw [Set.pair_comm (Work.Landing.angDouble b) (Work.Landing.angDouble a)]
  exact h'

/-- The two ends of the `j`-th lifted arc reduce, modulo `1`, to the two `j`-th iterates of the
root angles: the lifted arcs are the lifts of the ray pairs `angDouble^[j] {371,404}/1023`. -/
theorem wakeArc_endpoints (j : ℕ) :
    ({Int.fract (Work.Landing.wakeArc j).1, Int.fract (Work.Landing.wakeArc j).2} : Set ℝ)
      = {((Work.Landing.angDouble)^[j]) Work.Landing.rootAngle1,
         ((Work.Landing.angDouble)^[j]) Work.Landing.rootAngle2} := by
  induction j with
  | zero =>
    -- `wakeArc 0 = (371/1023, 404/1023)` and both entries already lie in `[0,1)`.
    norm_num [Work.Landing.wakeArc, Int.fract, Work.Landing.rootAngle1, Work.Landing.rootAngle2]
  | succ j ih =>
    -- `wakeArc_step` sends the doubled endpoints of `wakeArc j` to the (reversed) endpoints of
    -- `wakeArc (j+1)`; `angDouble_fract` removes the `Int.fract` on the inside.
    have h1 : Int.fract (Work.Landing.wakeArc (j + 1)).1
        = Work.Landing.angDouble (Int.fract (Work.Landing.wakeArc j).2) := by
      rw [← (wakeArc_step j).2, angDouble_fract, Work.Landing.angDouble]
    have h2 : Int.fract (Work.Landing.wakeArc (j + 1)).2
        = Work.Landing.angDouble (Int.fract (Work.Landing.wakeArc j).1) := by
      rw [← (wakeArc_step j).1, angDouble_fract, Work.Landing.angDouble]
    -- Unfold the `(j+1)`-st iterate into `angDouble` applied to the `j`-th iterate.
    have hR1 : (Work.Landing.angDouble)^[j + 1] Work.Landing.rootAngle1
        = Work.Landing.angDouble ((Work.Landing.angDouble)^[j] Work.Landing.rootAngle1) :=
      Function.iterate_succ_apply' _ _ _
    have hR2 : (Work.Landing.angDouble)^[j + 1] Work.Landing.rootAngle2
        = Work.Landing.angDouble ((Work.Landing.angDouble)^[j] Work.Landing.rootAngle2) :=
      Function.iterate_succ_apply' _ _ _
    show ({Int.fract (Work.Landing.wakeArc (j + 1)).1,
        Int.fract (Work.Landing.wakeArc (j + 1)).2} : Set ℝ)
      = {((Work.Landing.angDouble)^[j + 1]) Work.Landing.rootAngle1,
         ((Work.Landing.angDouble)^[j + 1]) Work.Landing.rootAngle2}
    rw [h1, h2, hR1, hR2]
    exact angDouble_pair_step _ _ _ _ ih

end Work.Landing.Angle
