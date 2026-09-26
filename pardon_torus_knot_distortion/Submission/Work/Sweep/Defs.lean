import Mathlib
import ChallengeDeps

/-!
# Integral geometry of a sweep: definitions

This file sets up the vocabulary for the integral-geometric estimates used in
Pardon's proof of the torus-knot distortion bound.

## Setting

Fix a smooth knot `K : Knot` (a `C^∞`, `2π`-periodic immersion of `ℝ` into `ℝ³`,
injective on `[0, 2π)`) with speed `speed K t = ‖deriv K.curve t‖`, arclength
`parameterArcLength` and intrinsic distance `intrinsicDistance`.  Write
`γ := K.curve`.

A real number `d` is a *distortion bound* for `K` (`IsDistortionBound K d`) if for
all parameters `s, t` in the fundamental interval the intrinsic distance along the
curve is at most `d` times the Euclidean distance of the two points.

## Contents

* `arclengthIn K E` — the arclength of the portion of the curve over a set `E` of
  parameters, defined as the Lebesgue integral of the speed over `E` (an extended
  nonnegative real, so that no integrability side conditions are ever needed).
* `paramSetIn K B` — the parameters of the fundamental interval `[0, 2π]` whose
  image lies in a target set `B ⊆ ℝ³`.
* `sphereParamSet K x r`, `sphereCount K x r` — the parameters at which the curve
  meets the sphere of centre `x` and radius `r`, and how many there are (as an
  extended nonnegative real: `⊤` if there are infinitely many).
* `coordParamSet K x R s`, `coordCount K x R s` — the same for the level sets
  `{y | y 2 = s}` of the third coordinate, cut out by the ball of radius `R`.
* `IsTransverseSphere` / `IsTransverseCoord` — transversality of the curve to
  those level sets, phrased as non-vanishing of the derivative of the relevant
  scalar function.

The companion files prove the four deliverables: the length bound
(`LengthInBall.lean`), the one-dimensional coarea formula (`Coarea.lean`,
`SweepCount.lean`), the existence of levels with few intersections
(`FewIntersections.lean`) and the a.e. transversality statement
(`Transversality.lean`).
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- `IsDistortionBound K d` says that `d` bounds all the distortion ratios of `K`
on the fundamental interval: the intrinsic distance along the curve is at most `d`
times the Euclidean distance.  This is the hypothesis under which every estimate
of this subproject is proved. -/
def IsDistortionBound (K : Knot) (d : ℝ) : Prop :=
  ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
    intrinsicDistance K s t ≤ d * dist (K.curve s) (K.curve t)

/-- The arclength of the portion of the curve lying over the parameter set `E`, as
an extended nonnegative real: the Lebesgue integral of the speed over `E`.

For `E` contained in a fundamental interval this is the total variation of the
curve over the corresponding parameter set.  Stated as an integral, it is the
quantity produced by the coarea formula. -/
def arclengthIn (K : Knot) (E : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in E, ENNReal.ofReal (speed K t)

/-- The parameters in the fundamental interval `[0, 2π]` whose image lies in `B`. -/
def paramSetIn (K : Knot) (B : Set R3) : Set ℝ :=
  K.curve ⁻¹' B ∩ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The parameters in the half-open fundamental interval `[0, 2π)` whose image
lies in `B`.  This is the form in which the distortion hypothesis
(`IsDistortionBound`, which quantifies over `Ico 0 (2π)`) applies; it differs
from `paramSetIn K B` only by the possible point `2π`. -/
def paramSetInIco (K : Knot) (B : Set R3) : Set ℝ :=
  K.curve ⁻¹' B ∩ Set.Ico (0 : ℝ) (2 * Real.pi)

/-- The parameters in the fundamental interval at which the curve meets the sphere
of centre `x` and radius `r`. -/
def sphereParamSet (K : Knot) (x : R3) (r : ℝ) : Set ℝ :=
  K.curve ⁻¹' Metric.sphere x r ∩ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The same set of parameters, using the half-open fundamental interval `[0, 2π)`.
It differs from `sphereParamSet` only by the possible point `2π`, so the two count
the same intersection points of the curve with the sphere. -/
def sphereParamSetIco (K : Knot) (x : R3) (r : ℝ) : Set ℝ :=
  K.curve ⁻¹' Metric.sphere x r ∩ Set.Ico (0 : ℝ) (2 * Real.pi)

/-- The number of parameters at which the curve meets the sphere of centre `x` and
radius `r`, as an extended nonnegative real (`⊤` when there are infinitely many). -/
def sphereCount (K : Knot) (x : R3) (r : ℝ) : ℝ≥0∞ :=
  ↑((sphereParamSet K x r).encard)

/-- The parameters in the fundamental interval at which the curve meets the plane
`{y | y 2 = s}` inside the open ball of centre `x` and radius `R`. -/
def coordParamSet (K : Knot) (x : R3) (R s : ℝ) : Set ℝ :=
  K.curve ⁻¹' (Metric.ball x R ∩ {y : R3 | y 2 = s}) ∩ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The number of parameters at which the curve crosses the plane `{y | y 2 = s}`
inside the ball of centre `x` and radius `R`, as an extended nonnegative real. -/
def coordCount (K : Knot) (x : R3) (R s : ℝ) : ℝ≥0∞ :=
  ↑((coordParamSet K x R s).encard)

/-- The curve is transverse to the sphere of centre `x` and radius `r` at every
intersection point: the radial distance function does not have vanishing derivative
there, i.e. the curve is not tangent to the sphere. -/
def IsTransverseSphere (K : Knot) (x : R3) (r : ℝ) : Prop :=
  ∀ t ∈ sphereParamSet K x r, deriv (fun u => dist (K.curve u) x) t ≠ 0

/-- The curve is transverse to the plane `{y | y 2 = s}` at every intersection point
inside the ball: the third coordinate function has non-vanishing derivative there. -/
def IsTransverseCoord (K : Knot) (x : R3) (R s : ℝ) : Prop :=
  ∀ t ∈ coordParamSet K x R s, deriv (fun u => (K.curve u) 2) t ≠ 0

end Work.Sweep
