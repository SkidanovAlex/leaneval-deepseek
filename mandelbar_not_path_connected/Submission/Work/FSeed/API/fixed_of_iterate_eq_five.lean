import Mathlib
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FSeed.API

/-- If `z` is periodic of period `5` and also periodic of some period `j` with `1 ≤ j < 5`,
then `z` is a fixed point of `f`.

Indeed `Function.IsPeriodicPt.gcd` shows that `z` is periodic of period `Nat.gcd 5 j`, and
`1 ≤ j < 5` forces `Nat.gcd 5 j = 1`. -/
theorem fixed_of_iterate_eq_five {f : ℂ → ℂ} {z : ℂ} {j : ℕ} (hj : 1 ≤ j) (hj5 : j < 5)
    (h5 : (f^[5]) z = z) (hjz : (f^[j]) z = z) : f z = z := by
  have h5' : Function.IsPeriodicPt f 5 z := h5
  have hj' : Function.IsPeriodicPt f j z := hjz
  have hg : Function.IsPeriodicPt f (Nat.gcd 5 j) z := h5'.gcd hj'
  have hgcd : Nat.gcd 5 j = 1 := by interval_cases j <;> norm_num
  rw [hgcd] at hg
  simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hg

end Work.FSeed.API
