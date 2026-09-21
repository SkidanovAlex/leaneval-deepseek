import Mathlib

/-!
# The envelope profile of the odd-dimensional Ulam construction

This file sets up the objects used to build the profile `f` of Ryabogin's odd-dimensional
counterexample (`d = 2n+1`) out of a *chord-endpoint curve* `(x, y)`.

Geometry.  Let `K_f = {x : x_0 ∈ [-1,1], Σ_{i>0} x_i² ≤ f (x_0)²}` be a body of revolution and
`L_s t = s * t + h s` a one-parameter family of lines in the `(x_0, x_d)`-plane.  The points of
intersection of the line `{z = L_s t}` with the *boundary* of the planar section
`{(t,z) : |z| ≤ f t}` are the points `(y s, f (y s))` (on the upper boundary) and
`(-(x s), -(f (-(x s))))` (on the lower boundary); thus

  `f (y s) = s * y s + h s`,   `f (-(x s)) = s * x s - h s`.

Conversely, the profile is *recovered* from the curve `(x,y)`:  for `t > 0` let `σ = σ_y(t)` be
the unique slope whose right intersection has first coordinate `t` (`y σ = t`), and put
`f t = σ * t + h σ`;  for `t < 0` let `σ = σ_x(t)` be the unique slope with `x σ = -t` and put
`f t = -(σ * t + h σ)`.  That is `envelopeProfile` below.  For `|t| ≥ 1` the profile is zero; at
`t = 0` it is `1` (the limit of both branches).

## Main definitions

* `profileX` — the chord-endpoint function of the unit semicircle, `s ↦ 1/√(1+s²)`.
* `tau` — the threshold `τ = 1/10` of the paper.
* `slopeRight`, `slopeLeft` — the inverses of `y` resp. of `t ↦ -x t` on `(0,∞)`.
* `envelopeRight`, `envelopeLeft`, `envelopeProfile` — the two branches and the profile.
* `IsEnvelopeCurve h x y` — the complete hypothesis package on `(h,x,y)` used by the main
  theorem `Work.OddEnvelope.odd_envelope_profile`.

## Conventions

Throughout, `s`, `σ` denote *slopes* (living in `(0,∞)`) and `t` denotes the first coordinate
(so `t ∈ (-1,1)` on the body).  All the hypotheses of `IsEnvelopeCurve` are stated on `(0,∞)`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- The chord-endpoint function of the unit semicircle: `x_o s = y_o s = 1/√(1+s²)`. -/
def profileX (s : ℝ) : ℝ := 1 / Real.sqrt (1 + s ^ 2)

/-- The threshold `τ = 1/10` of the paper. -/
def tau : ℝ := 1 / 10

/-- The (unique, when it exists) slope `σ > 0` with `y σ = t`: the inverse of `y` on `(0,∞)`. -/
def slopeRight (y : ℝ → ℝ) (t : ℝ) : ℝ := Function.invFunOn y (Set.Ioi 0) t

/-- The (unique, when it exists) slope `σ > 0` with `x σ = -t`; used for `t < 0`. -/
def slopeLeft (x : ℝ → ℝ) (t : ℝ) : ℝ := Function.invFunOn x (Set.Ioi 0) (-t)

/-- The right branch of the envelope profile: `t ↦ σ t + h σ` with `y σ = t`. -/
def envelopeRight (h y : ℝ → ℝ) (t : ℝ) : ℝ := slopeRight y t * t + h (slopeRight y t)

/-- The left branch of the envelope profile: `t ↦ -(σ t + h σ)` with `x σ = -t`. -/
def envelopeLeft (h x : ℝ → ℝ) (t : ℝ) : ℝ := -(slopeLeft x t * t + h (slopeLeft x t))

/-- **The envelope profile** built from the chord-endpoint curve `(x, y)` and the perturbation
`h`.  It equals `envelopeRight h y` on `(0,1)`, `envelopeLeft h x` on `(-1,0)`, is `1` at `0`
and `0` outside `[-1,1]`. -/
def envelopeProfile (h x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ Set.Ioo (0 : ℝ) 1 then envelopeRight h y t
  else if t ∈ Set.Ioo (-1 : ℝ) 0 then envelopeLeft h x t
  else if t = 0 then 1 else 0


/-- The unit semicircle profile `t ↦ √(1-t²)`: the profile produced by the unperturbed chord
curve `x = y = profileX`, `h = 0`. -/
def semicircle (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

/-- The logarithmic-derivative function of the right branch,
`K σ = (y σ + σ y' σ + h' σ) / y' σ`, characterised by
`deriv (envelopeRight h y) t = kSlope h y (slopeRight y t)`. -/
def kSlope (h y : ℝ → ℝ) (σ : ℝ) : ℝ := (y σ + σ * deriv y σ + deriv h σ) / deriv y σ

/-- The half-width of the unperturbed part of the profile: the image of `[1-τ, ∞)` under the
chord function `profileX` of the semicircle. -/
def tStar : ℝ := profileX (1 - tau)

/-- The right branch of the profile, applied with the reflected perturbation: this is the left
branch of the profile. -/
def negH (h : ℝ → ℝ) : ℝ → ℝ := fun σ => -h σ

/-- **The hypothesis package on the chord-endpoint curve.**  `h` is the perturbation (a smooth
bump supported in `[1-2τ, 1-τ]`), and `x`, `y` are the two chord-endpoint functions.

The `mono_*` fields say that `s ↦ s * y s + h s` and `s ↦ s * x s - h s` are strictly increasing
(so that the two branches of the profile are positive and the profile decreases away from `0`),
and the `shape_*` fields are the second-order conditions expressing that the profile is strictly
concave (they are exactly `deriv (deriv f) < 0` on the two branches, written in terms of the
curve; they hold whenever `(x,y)` is `C²`-close to the semicircle — see
`Work.OddEnvelope.isEnvelopeCurve_of_close`). -/
structure IsEnvelopeCurve (h x y : ℝ → ℝ) : Prop where
  /-- `h` is smooth on `(0,∞)`. -/
  smooth_h : ContDiffOn ℝ ∞ h (Set.Ioi 0)
  /-- `x` is smooth on `(0,∞)`. -/
  smooth_x : ContDiffOn ℝ ∞ x (Set.Ioi 0)
  /-- `y` is smooth on `(0,∞)`. -/
  smooth_y : ContDiffOn ℝ ∞ y (Set.Ioi 0)
  /-- `h 0 = 0`. -/
  h_zero : h 0 = 0
  /-- `h` is supported in the window `[1-2τ, 1-τ]`. -/
  h_support : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)
  /-- `x` is strictly decreasing on `(0,∞)`. -/
  x_deriv_neg : ∀ s, 0 < s → deriv x s < 0
  /-- `y` is strictly decreasing on `(0,∞)`. -/
  y_deriv_neg : ∀ s, 0 < s → deriv y s < 0
  /-- `x s → 1` as `s → 0⁺` (the chord through the right end of the profile). -/
  x_tendsto_one : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 1)
  /-- `y s → 1` as `s → 0⁺`. -/
  y_tendsto_one : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1)
  /-- Beyond the perturbation window the curve is the semicircle. -/
  x_tail : ∀ s, 1 - tau ≤ s → x s = profileX s
  /-- Beyond the perturbation window the curve is the semicircle. -/
  y_tail : ∀ s, 1 - tau ≤ s → y s = profileX s
  /-- `s ↦ s * y s + h s` is strictly increasing. -/
  mono_y : ∀ s, 0 < s → 0 < y s + s * deriv y s + deriv h s
  /-- `s ↦ s * x s - h s` is strictly increasing. -/
  mono_x : ∀ s, 0 < s → 0 < x s + s * deriv x s - deriv h s
  /-- Second-order shape condition on the right branch (concavity of `f` on `(0,1)`). -/
  shape_y : ∀ s, 0 < s →
    0 < 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s +
      deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s
  /-- Second-order shape condition on the left branch (concavity of `f` on `(-1,0)`). -/
  shape_x : ∀ s, 0 < s →
    0 < 2 * (deriv x s) ^ 2 - x s * deriv (deriv x) s -
      deriv (deriv h) s * deriv x s + deriv h s * deriv (deriv x) s

end

end Work.OddEnvelope
