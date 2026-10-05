import Mathlib
import Submission.Work.RPB.B2.PhaseDefs

/-!
# Reflection of the divided chord under the chord swap

For a curve family `c` that is `2π`-periodic in its parameter, the chord swap
`(t, r) ↦ (t + π, π - r)` reverses the chord direction: the chord vector
`chordVec c τ (t+π) (π-r)` is `- chordVec c τ t r`.  Dividing by `r` (with `chordW = chordVec / r`)
this gives the *weighted* reflection law of the divided chord `chordW` (and of its `τ`-derivative
`chordWd`):

  `chordW c τ (t+π) (π-r) = -(r/(π-r)) · chordW c τ t r`

for `0 < r < π`, and the same identity for `chordWd` since the scalar factor does not depend on `τ`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-- The chord swap reverses the chord vector. -/
theorem chordVec_swap (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * π) = c τ t) (τ t r : ℝ) :
    Work.RPB.chordVec c τ (t + π) (π - r) = -Work.RPB.chordVec c τ t r := by
  rw [Work.RPB.chordVec, Work.RPB.chordVec]
  have h1 : t + π + (π - r) = (t - r) + 2 * π := by ring
  have h2 : t + π - (π - r) = t + r := by ring
  rw [h1, h2, hper τ (t - r)]
  ring

end Work.RPB.B2
