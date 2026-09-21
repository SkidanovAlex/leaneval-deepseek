import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddRadon.Core

/-!
# `Work.OddCurve.LowSlope` — the low-slope step of the odd-dimensional case (paper Step 3)

This chapter carries the mathematics of the *low slopes* `0 < s ≤ 1 - 2τ` of Ryabogin's odd
case.  On that range the bump `h` vanishes (`Function.support h ⊆ Icc (1-2τ) (1-τ)` and `h` is
flat at the left edge of its support), so the cutting line is `L_s t = s t` and the two moment
equations take the *unshifted* form

* `(A)  ∫_{-x s}^{y s} (f² - (s t)²)^{n+1/2} dt = C / √(1+s²)`,
* `(B)  ∫_{-x s}^{y s} (f² - (s t)²)^{n-1/2} t dt = 0`.

The paper does not obtain these from the Volterra system (whose kernel degenerates like
`s^{n±1/2}` as `s → 0`, see the workspace notes); it constructs the remaining part of the
*profile* through the spherical Radon transform, and concludes the moment equations by

* Proposition `workHARD1` (the Radon data of a body of revolution are the second moments of its
  central sections), and
* Lemma `cl1` (given the centroid condition `(cmass)` and the inertia condition `(i1)`, the
  moment condition `(ij)` = `(A)` follows on the range in question by a one-dimensional ODE).

This file fixes the vocabulary of that step: the three section integrals `centIntegral` (`(cmass)`)
`inertiaIntegral` (`(i1)`) and `momentIntegral` (`(ij)` = `(A)`) in the unshifted form, their
relation to `Work.OddCurve.momentA`/`momentB`, and the two constants of the ball
(`refConst` and `ballInertiaConst`) together with the integration-by-parts identity
`refConst n = (2*n+1) * ballInertiaConst n` that makes the constants agree
(`Work.OddCurve.LowSlope.refConst_eq_inertia`).

## Conventions

* `n ≥ 1`, `d = 2n+1`; the profile is `f`, the chord curve is `(x,y)`, and on the low-slope range
  the cutting line is `s t` (no `h`).
* All exponents are written with `√`: `(f² - (s t)²)^{n-1/2}` is
  `(f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * √(f t ^ 2 - (s * t) ^ 2)`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The volume of the unit ball of `ℝ ^ m`, `|B^m|`. -/
def ballVol (m : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal

/-- The radicand of the low-slope section integrals: `f t ^ 2 - (s * t) ^ 2`.  This is
`Work.OddCurve.rad h f s t` when `h s = 0`. -/
def rad0 (f : ℝ → ℝ) (s t : ℝ) : ℝ := f t ^ 2 - (s * t) ^ 2

/-- The **centroid integral** `(cmass)` of the paper (Lemma `FL`), in the low-slope (`h ≡ 0`)
regime, at exponent `(d-2)/2 = n - 1/2`:
`∫_{-x s}^{y s} t (f t² - (s t)²)^{n-1/2} dt`.
The centroid condition is `centIntegral n f x y s = 0`. -/
def centIntegral (n : ℕ) (f x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-(x s))..(y s),
    t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t)

/-- The **inertia integral** `(i1)` of the paper (Lemma `FL`), low-slope regime:
`∫_{-x s}^{y s} t² (f t² - (s t)²)^{n-1/2} dt`.
The inertia condition is `(1+s²)^{3/2} * inertiaIntegral n f x y s = const`. -/
def inertiaIntegral (n : ℕ) (f x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-(x s))..(y s),
    t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t)

/-- The **moment integral** `(ij)` of the paper (Lemma `FL`), low-slope regime, at exponent
`d/2 = n + 1/2`: `∫_{-x s}^{y s} (f t² - (s t)²)^{n+1/2} dt`.
This is exactly `Work.OddCurve.momentA n h x y f s` when `h s = 0`. -/
def momentIntegral (n : ℕ) (f x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-(x s))..(y s),
    rad0 f s t ^ n * Real.sqrt (rad0 f s t)

/-- **The ball's inertia constant** `∫_{-1}^{1} u² (1-u²)^{n-1/2} du`: the constant `I₁` of the
inertia condition `(i1)` for the semicircle. -/
def ballInertiaConst (n : ℕ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)

@[simp] lemma rad0_eq_rad (h f : ℝ → ℝ) {s : ℝ} (hs : h s = 0) (t : ℝ) :
    Work.OddCurve.rad h f s t = rad0 f s t := by
  simp [Work.OddCurve.rad, rad0, hs]

/-- On the low-slope range `momentA` is the unshifted moment integral. -/
lemma momentA_eq_momentIntegral {n : ℕ} {h f x y : ℝ → ℝ} {s : ℝ} (hs : h s = 0) :
    Work.OddCurve.momentA n h x y f s = momentIntegral n f x y s := by
  rw [Work.OddCurve.momentA, momentIntegral]
  exact intervalIntegral.integral_congr (fun t _ => by rw [rad0_eq_rad h f hs t])

/-- On the low-slope range `momentB` is the unshifted centroid integral. -/
lemma momentB_eq_centIntegral {n : ℕ} {h f x y : ℝ → ℝ} {s : ℝ} (hs : h s = 0)
    (hds : deriv h s = 0) :
    Work.OddCurve.momentB n h x y f s = centIntegral n f x y s := by
  rw [Work.OddCurve.momentB, centIntegral]
  exact intervalIntegral.integral_congr (fun t _ => by
    rw [rad0_eq_rad h f hs t, hds, add_zero]; ring)

/-- The two equations `(A)`, `(B)` of the paper in the **unshifted** low-slope form, with the
ball's constants.  This is the package that `Work.OddCurve.LowSlope.cl1` converts into the moment
equation `(A)` on the whole range. -/
def LowSlopeHyp (n : ℕ) (f x y : ℝ → ℝ) (S : Set ℝ) : Prop :=
  (∀ s ∈ S, centIntegral n f x y s = 0) ∧
    (∀ s ∈ S, (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * inertiaIntegral n f x y s = ballInertiaConst n)

/-- The conclusion of the low-slope step: the moment equation `(A)` with the ball's constant. -/
def LowSlopeConcl (n : ℕ) (f x y : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, Real.sqrt (1 + s ^ 2) * momentIntegral n f x y s = refConst n

end

end Work.OddCurve.LowSlope
