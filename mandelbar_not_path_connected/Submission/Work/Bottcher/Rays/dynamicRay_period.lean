import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Rays

/-- The dynamic ray `R_c(θ)` is periodic in the angle with period `1`: this is
immediate from the definition, since the ray only depends on the direction
`rayDirection θ = exp(2πiθ)` of the Böttcher coordinate, and
`rayDirection (θ + 1) = rayDirection θ`. -/
theorem dynamicRay_period (c : ℂ) (θ : ℝ) :
    Work.Bottcher.dynamicRay c (θ + 1) = Work.Bottcher.dynamicRay c θ := by
  unfold Work.Bottcher.dynamicRay
  rw [Work.Bottcher.rayDirection_add_one]

end Work.Bottcher.Rays
