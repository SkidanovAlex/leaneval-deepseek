import Mathlib
import Submission.Work.RPB.Defs

/-!
# B2: definitions for the chord phase of a curve isotopy

This file holds the definitions used by `Work.RPB.B2.chordPhase_exists`, the B2 node of the
rectangular-peg route: the construction of a smooth lift `a` of `arg (c τ (t+r) - c τ (t-r))`
on the strip `0 ≤ τ ≤ 1`, `0 < r ≤ π`.

The construction is the `τ`-ray integral of the logarithmic derivative of the chord vector, but
`q = Im(conj v ∂_τ v)/‖v‖²` itself is singular at `r = 0` and `r = π` (where the chord vector
vanishes).  The fix encoded here is to *divide out* the linear vanishing:

* `chordW c τ t r = ∫_{s ∈ [-1,1]} c'(t + s r) ds` is the smooth divided chord, satisfying
  `chordVec c τ t r = r * chordW c τ t r` for all `τ, t, r`; near `r = 0` it is non-vanishing.
* the reflection `(τ,t,r) ↦ (τ, t+π, π-r)` sends `chordVec` to `-chordVec` (periodicity of `c`),
  so `chordQ c τ (t+π) (π-r) = chordQ c τ t r`; using this second chart removes the `r = π`
  singularity.
* `cut0`, `cut1` are the `r`-cut-offs gluing the two charts; they sum to `1` on `(0,π)`.
* `cutTau δ` is a `τ`-cut-off, equal to `1` on `[0,1]` and supported in `(-δ, 1+δ)`; it makes the
  assembled integrand `chordG` globally smooth even though `chordW` can vanish for `τ ∉ [0,1]`.
* `chordA c δ τ t r = t + π/2 + τ * ∫_{σ ∈ [0,1]} chordG c δ (τ*σ) t r dσ` is the candidate phase;
  for `τ ∈ [0,1]` the substitution `σ ↦ τ*σ` turns it into `t + π/2 + ∫_0^τ q`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-- The divided chord `W = chordVec / r`, presented as the integral of the tangent,
`W τ t r = ∫_{s ∈ [-1,1]} c'(t + s r) ds`.  It satisfies `chordVec c τ t r = r * W τ t r` and is
smooth across `r = 0` (where it equals `2 c'(t)`). -/
def chordW (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ :=
  ∫ s in (-1 : ℝ)..1, deriv (fun u => c τ u) (t + s * r)

/-- The `τ`-derivative of `chordW`, kept as a separate definition so that its smoothness can be
stated as a self-contained lemma. -/
def chordWd (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ :=
  deriv (fun σ => chordW c σ t r) τ

/-- `q = Im(conj W ∂_τ W)/‖W‖² = ∂_τ arg W`: the logarithmic derivative of `chordW`, which is the
smooth version of `∂_τ arg (chordVec)` away from its two singularities.  (Division is Lean's total
division, so the function is `0` wherever `chordW` vanishes; it is smooth on `{chordW ≠ 0}`.) -/
def chordQ (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℝ :=
  Work.RPV.ωC (chordW c τ t r) (chordWd c τ t r) / ‖chordW c τ t r‖ ^ 2

/-! ## the two cut-offs in `r` -/

/-- the cut-off supported in `[1, 9/2]`, equal to `1` on `[2, 7/2]`. -/
def cut1 (r : ℝ) : ℝ :=
  Real.smoothTransition (r - 1) * Real.smoothTransition (4.5 - r)

/-- the cut-off supported in `[-2, 3]`, equal to `1` on `[-1, 2]`. -/
def cutEta (r : ℝ) : ℝ :=
  Real.smoothTransition (r + 2) * Real.smoothTransition (3 - r)

/-- the cut-off on the `r = 0` chart. -/
def cut0 (r : ℝ) : ℝ := (1 - cut1 r) * cutEta r

/-- the cut-off in `τ`, supported in `(-δ/2, 1 + δ/2)`, equal to `1` on `[0,1]`. -/
def cutTau (δ τ : ℝ) : ℝ :=
  Real.smoothTransition (1 + 2 * (τ / δ)) * Real.smoothTransition (1 + 2 * ((1 - τ) / δ))

/-- The assembled integrand: the two charts glued by the `r`-cut-offs and cut off in `τ`.  For
`τ ∈ [0,1]` and `r ∈ (0,π)` it equals `chordQ c τ t r`. -/
def chordG (c : ℝ → ℝ → ℂ) (δ : ℝ) (τ t r : ℝ) : ℝ :=
  cutTau δ τ * cut0 r * chordQ c τ t r + cutTau δ τ * cut1 r * chordQ c τ (t + π) (π - r)

/-- The candidate chord phase.  For `τ ∈ [0,1]` and `r ∈ (0,π)` it equals
`t + π/2 + ∫_0^τ Im(conj v ∂_τ v)/‖v‖²`, `v = chordVec c · t r`. -/
def chordA (c : ℝ → ℝ → ℂ) (δ : ℝ) (τ t r : ℝ) : ℝ :=
  t + π / 2 + τ * ∫ σ in (0 : ℝ)..1, chordG c δ (τ * σ) t r

end Work.RPB.B2
