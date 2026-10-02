import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- `angDouble` depends only on `θ mod 1`: the fractional-part normalisation `θ ↦ Int.fract θ`
does not change `Int.fract (-2 * θ)`.

Indeed `θ = Int.fract θ + ⌊θ⌋`, hence `-2 * θ = -2 * Int.fract θ - (2 * ⌊θ⌋ : ℤ)`, and
`Int.fract` is invariant under subtracting an integer. -/
theorem angDouble_fract (θ : ℝ) :
    Work.Landing.angDouble (Int.fract θ) = Work.Landing.angDouble θ := by
  simp only [Work.Landing.angDouble]
  conv_rhs => rw [← Int.fract_add_floor θ]
  rw [show -2 * (Int.fract θ + (⌊θ⌋ : ℝ)) = -2 * Int.fract θ - ((2 * ⌊θ⌋ : ℤ) : ℝ) by
        push_cast; ring]
  rw [Int.fract_sub_intCast]

end Work.Landing.Angle
