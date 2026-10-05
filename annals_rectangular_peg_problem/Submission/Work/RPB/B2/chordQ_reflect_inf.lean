import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.chordVec_eq_mul_chordW_inf
import Submission.Work.RPB.B2.chordW_chordWd_reflect_inf
import Submission.Work.RPB.B2.omegaC_real_scale

/-!
# The chord phase `q` is invariant under the reflection `(t, r) ↦ (t + π, π - r)` (`C^∞` version)

`chordQ c τ t r = Im(conj W ∂_τ W)/‖W‖²` with `W = chordW c τ t r` is the logarithmic derivative
`∂_τ arg (chord direction)` of the chord from `c τ (t - r)` to `c τ (t + r)`.

The reflection `(t, r) ↦ (t + π, π - r)` swaps the two endpoints of the chord: by `2π`-periodicity
of `c`,

  `chordVec c τ (t + π) (π - r) = c τ (t + 2π - r) - c τ (t + r) = c τ (t - r) - c τ (t + r)`
  `                             = - chordVec c τ t r`,

so the reflected chord is the *negative* of the original one, i.e. the divided chord is rescaled by
the (real, negative) constant `-(r/(π-r))`.  Since `chordQ` is unchanged by multiplying `W` by a
nonzero real constant depending only on `τ` (`‖·‖²` and `Im(conj · ∂_τ ·)` both pick up `l²`, which
cancels), the reflection leaves `chordQ` invariant.

This is the `C^∞` ("`inf`") variant of `chordQ_reflect`: the only smoothness input is the divided
chord identity `chordVec = r · chordW`, which is available for the exponent `∞ = ((⊤ : ℕ∞) :
WithTop ℕ∞)` in `chordVec_eq_mul_chordW_inf` (it needs only differentiability plus continuity of the
derivative, i.e. the fundamental theorem of calculus).  The rescaling of `chordW` (and of its
`τ`-derivative `chordWd`) is `chordW_chordWd_reflect_inf` and the cancellation is
`omegaC_real_scale`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

theorem chordQ_reflect_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) (τ t r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Work.RPB.B2.chordQ c τ (t + Real.pi) (Real.pi - r) = Work.RPB.B2.chordQ c τ t r := by
  -- the reflection rescales the divided chord and its `τ`-derivative by the same real factor
  obtain ⟨hW, hWd⟩ := chordW_chordWd_reflect_inf c hc hper τ t r hr
  -- the factor is nonzero since `0 < r < π`
  have hr0 : (r / (Real.pi - r) : ℝ) ≠ 0 :=
    div_ne_zero (ne_of_gt hr.1) (ne_of_gt (sub_pos.mpr hr.2))
  have hl : (-(r / (Real.pi - r)) : ℝ) ≠ 0 := neg_ne_zero.mpr hr0
  -- the common factor cancels in `Im(conj W ∂_τ W)/‖W‖²`
  rw [chordQ, chordQ, hW, hWd]
  exact omegaC_real_scale (-(r / (Real.pi - r))) (chordW c τ t r) (chordWd c τ t r) hl

end Work.RPB.B2
