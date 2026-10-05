import Mathlib
import Submission.Work.RPB.B1a.Defs

/-!
# `Work.RPB.B1a`: the straightening half-balls

Vocabulary shared by the players of the local half-disk lemma for a smooth loop.

For `v : ℝ → ℂ` a smooth immersed loop and `t₀` a parameter with `deriv v t₀ ≠ 0`, the
*straightening map* is

`straightenMap v t₀ p = v (t₀ + p.1) + p.2 * (I * deriv v t₀)`,

the standard "normal bundle" chart at the point `v t₀`: the horizontal axis `p.2 = 0` is carried to
the curve, and the vertical direction to the normal direction `I * (deriv v t₀)`.

The two half-balls are the images of the two local sides, cut down to the ball of radius
`2ρ/‖deriv v t₀‖` (the size within which the chart is a genuine chart at scale `ρ`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Complex Set Metric

/-- The straightening map at the parameter `t₀` of the loop `v`. -/
def straightenMap (v : ℝ → ℂ) (t₀ : ℝ) : ℝ × ℝ → ℂ :=
  fun p => v (t₀ + p.1) + (p.2 : ℂ) * (Complex.I * deriv v t₀)

/-- The upper half-ball of the straightening at `t₀`, cut to `ball 0 (2ρ/‖deriv v t₀‖)`. -/
def halfBallUp (g : ℝ → ℂ) (w : ℂ) (ρ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 < p.2 ∧ ‖g p.1 + (p.2 : ℂ) * (Complex.I * w)‖ < ρ} ∩
    Metric.ball 0 (2 * ρ / ‖w‖)

/-- The lower half-ball of the straightening at `t₀`, cut to `ball 0 (2ρ/‖deriv v t₀‖)`. -/
def halfBallDn (g : ℝ → ℂ) (w : ℂ) (ρ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.2 < 0 ∧ ‖g p.1 + (p.2 : ℂ) * (Complex.I * w)‖ < ρ} ∩
    Metric.ball 0 (2 * ρ / ‖w‖)

end Work.RPB.B1a
