/-
# `saw (x + 1) = saw x`

The triangle wave `saw x = 1/2 - 2 |fract (x + 1/4) - 1/2|` of `Work.FQC.Defs` is
`1`-periodic.  This is what makes the MNS twist `ℓ_t` commute with the shift
`w ↦ w + 1` of the Écalle cylinder.

Since `saw` is a function of `Int.fract (x + 1/4)` alone and `Int.fract` is invariant
under adding `1` (`Int.fract_add_one`), the shift by `1` leaves `saw` unchanged.
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQC

theorem saw_add_one (x : ℝ) : Work.FQC.saw (x + 1) = Work.FQC.saw x := by
  rw [saw_apply, saw_apply, show x + 1 + 1 / 4 = (x + 1 / 4) + 1 by ring,
    Int.fract_add_one]

end Work.FQC
