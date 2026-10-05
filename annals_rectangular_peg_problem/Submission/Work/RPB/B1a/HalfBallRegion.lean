import Mathlib
import Submission.Work.RPB.B1a.HalfBallDefs

/-!
# `Work.RPB.B1a`: the sheared half-disk region

Vocabulary for the proof that the straightening half-balls `halfBallUp`/`halfBallDn` are
preconnected for small radius.

For a real function `g` (the local displacement of a loop, `g 0 = 0`, `g'(0) = w ≠ 0`) and a
radius `ρ`, the two half-balls are the two local sides of the straightening chart.  Writing

`h(x) = I * g x / w`  (`= hArg g w x`),  `hRe g w x = (h x).re`,  `hIm g w x = (h x).im`,

one has the identity

`‖g x + y * (I * w)‖ = ‖w‖ * |y - h x|`   for real `y`,

so that (for `ρ ≥ 0`)

`halfBallUp g w ρ = {p | 0 < p.2 ∧ (p.2 - P p.1)^2 + (Q p.1)^2 < r^2 ∧ p.1^2 + p.2^2 < 4 r^2}`

with `P = hRe g w`, `Q = hIm g w`, `r = ρ / ‖w‖`: the region `shearRegion P Q r`.

The analytic content is that `P = O(x^2)` and `Q = x + O(x^2)` (`Q` comparable to `±x`), which
makes the region a half-disk-like set: vertically it is an interval with upper boundary
`P x + sqrt (r^2 - Q x^2) ≤ r`, and the function `x ↦ (y - P x)^2 + (Q x)^2` is monotone on each
side of `0`.  The region is then preconnected: the point `(0,y)` lies in it for every `y ∈ (0,r)`
(the "spine"), and every point of the region can be joined horizontally to the spine.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Complex Set Metric

/-- The sheared half-disk region of radius `r` cut by the curve `x ↦ (Q x, P x)`:
the set of `p` with `p.2 > 0`, `(p.2 - P p.1)^2 + (Q p.1)^2 < r^2`, inside the ball of radius
`2 r` (the ball being taken in `ℝ × ℝ` with its product norm `‖p‖ = max |p.1| |p.2|`, so that this
is literally the ball occurring in `halfBallUp`/`halfBallDn`; note `‖p‖ < 2 r` gives in particular
`|p.1| < 2 r`). -/
def shearRegion (P Q : ℝ → ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    0 < p.2 ∧ (p.2 - P p.1) ^ 2 + (Q p.1) ^ 2 < r ^ 2 ∧ p ∈ Metric.ball (0 : ℝ × ℝ) (2 * r)}

/-- `I * g x / w`, the straightening coordinate: `‖g x + y (I w)‖ = ‖w‖ * ‖y - hArg g w x‖`. -/
def hArg (g : ℝ → ℂ) (w : ℂ) : ℝ → ℂ := fun x => Complex.I * g x / w

/-- The real part of the straightening coordinate. -/
def hRe (g : ℝ → ℂ) (w : ℂ) : ℝ → ℝ := fun x => (hArg g w x).re

/-- The imaginary part of the straightening coordinate. -/
def hIm (g : ℝ → ℂ) (w : ℂ) : ℝ → ℝ := fun x => (hArg g w x).im

/-- The real part of the derivative of the straightening coordinate. -/
def hDre (g : ℝ → ℂ) (w : ℂ) : ℝ → ℝ := fun x => (Complex.I * deriv g x / w).re

/-- The imaginary part of the derivative of the straightening coordinate. -/
def hDim (g : ℝ → ℂ) (w : ℂ) : ℝ → ℝ := fun x => (Complex.I * deriv g x / w).im

lemma hArg_apply (g : ℝ → ℂ) (w : ℂ) (x : ℝ) : hArg g w x = Complex.I * g x / w := rfl

lemma hRe_apply (g : ℝ → ℂ) (w : ℂ) (x : ℝ) : hRe g w x = (Complex.I * g x / w).re := rfl

lemma hIm_apply (g : ℝ → ℂ) (w : ℂ) (x : ℝ) : hIm g w x = (Complex.I * g x / w).im := rfl

lemma shearRegion_def (P Q : ℝ → ℝ) (r : ℝ) :
    shearRegion P Q r =
      {p : ℝ × ℝ |
        0 < p.2 ∧ (p.2 - P p.1) ^ 2 + (Q p.1) ^ 2 < r ^ 2 ∧
          p ∈ Metric.ball (0 : ℝ × ℝ) (2 * r)} :=
  rfl

lemma mem_shearRegion {P Q : ℝ → ℝ} {r : ℝ} {p : ℝ × ℝ} :
    p ∈ shearRegion P Q r ↔
      0 < p.2 ∧ (p.2 - P p.1) ^ 2 + (Q p.1) ^ 2 < r ^ 2 ∧
        p ∈ Metric.ball (0 : ℝ × ℝ) (2 * r) :=
  Iff.rfl

end Work.RPB.B1a
