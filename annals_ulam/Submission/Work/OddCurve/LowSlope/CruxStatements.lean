import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# The remaining crux of Step 3, as `Prop`s

The low-slope chapter (`LowSlope/README.md`) proves, sorry-free:

* `Work.OddCurve.LowSlope.cl1` — the paper's Lemma 4.2 converse;
* `Work.OddCurve.LowSlope.lowSlope_momentEqs` — from the two *section* conditions `(cmass)`, `(i1)`
  plus one value of `(A)`, obtain both moment equations on the low-slope range;
* `Work.OddCurve.LowSlope.smallSlopeCurveExistsStrong_of_halves` — the assembly.

What is still missing is the *construction* of the profile whose section conditions on the low
slopes are the ball's — the spherical-Radon step of the paper.  Its mathematical content is
isolated by the two `Prop`s below (so that the statements live in the API and can be delegated
without carrying a `sorry`).  Both were reviewed by two mathematicians each and checked
numerically (`_mylogs_ibp_check.py`, `_mylogs_radon_check.py`, `_mylogs_radon_check2.py` in the
workspace root).

* `SectionIBP` — the integration-by-parts identity
  `(d-2) ∫ t² f (f - t f') R^{(d-4)/2} = (d+1) ∫ t² R^{(d-2)/2}` on the chord (`R = f² - s²t²`,
  `d = 2n+1`).  Proof: `f (f - t f') = R - (t/2) R'` and
  `d/dt [t³ R^{(d-2)/2}] = 3 t² R^{(d-2)/2} + ((d-2)/2) t³ R' R^{(d-4)/2}`, with the boundary term
  vanishing at both ends of the chord; equivalently the difference
  `(d-2)·(first integrand) - (d+1)·(second integrand)` is `-d/dt [t³ R^{(d-2)/2}]`.  The two
  `IntervalIntegrable` hypotheses are those of the review: without them `deriv f` may be wild
  enough that the first integrand (which for `n = 1` has an integrable `R^{-1/2}` endpoint
  singularity) fails to be integrable.  For a strictly concave profile with `f y = s y`,
  `f (-x) = -(s(-x))` they follow from `R'(y) ≠ 0 ≠ R'(-x)` — i.e. from the chord being a genuine
  chord of a strictly convex body (a separate obligation for the caller).

* `RadonDataEqInertiaIntegral` — Prop. `workHARD1` of Ryabogin's paper in one dimension: the
  spherical-Radon data of a body of revolution are the second moments of its central sections,
  hence the low-slope inertia integral.  Proof: substitute `u = cos α · ν`, then
  `t = ρ u · u` (a `C¹` bijection onto the chord), and finish with `SectionIBP` and
  `|S^{d-3}| = (d-2)|B^{d-2}|`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The integration-by-parts identity of Prop. `workHARD1`** (one-dimensional form), with the
integrability side conditions of the review. -/
def SectionIBP : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) (x y s : ℝ),
    0 < s →
    ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1) →
    -(x) ∈ Set.Ioo (-1 : ℝ) 1 → y ∈ Set.Ioo (-1 : ℝ) 1 → -(x) < y →
    f y = s * y → f (-(x)) = -(s * (-(x))) →
    (∀ t ∈ Set.Ioo (-(x)) y, 0 < rad0 f s t) →
    IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x)) y →
    IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x)) y →
    (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 2) * (∫ t in (-(x))..y, t ^ 2 * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t))

/-- **Prop. `workHARD1` in one dimension**: the spherical-Radon data of a body of revolution are
the second moments of its central sections, i.e. they equal `(d+1)|B^{d-2}|√(1+s²)` times the
low-slope inertia integral.

The hypotheses are the ones the change of variables `t = ρ(u)·u` needs (see the proof sketch in
`LowSlope/README.md`): `f` is `C¹` on `[-1,1]` and `ρ` is the radial function (`f (ρ u · u) = ρ u √(1-u²)`, positive, `C¹`),
`u ↦ ρ u · u` is strictly increasing with non-vanishing derivative on `(-cos α, cos α)`
(`cos α = (√(1+s²))⁻¹`), and it maps the two ends of that interval onto the two ends of the chord
(`ρ (cos α)·cos α = y s`, `ρ (-cos α)·(-cos α) = -(x s)`), so that it is a `C¹` bijection onto the
chord. -/
def RadonDataEqInertiaIntegral : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (f ρ x y : ℝ → ℝ) (s : ℝ),
    0 < s →
    ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1) →
    (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) →
    ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) →
    StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) →
    (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) →
    (∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u) →
    ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s →
    ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s) →
    (∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈ Set.Ioo (-(x s)) (y s)) →
    -(x s) ∈ Set.Ioo (-1 : ℝ) 1 →
    y s ∈ Set.Ioo (-1 : ℝ) 1 →
    f (y s) = s * y s → f (-(x s)) = s * x s →
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = y s) →
    (∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(x s)) →
    -(x s) < y s →
    (∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < rad0 f s t) →
    IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
    IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
    Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ 2 *
            ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
      = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) *
        Real.sqrt (1 + s ^ 2) * inertiaIntegral n f x y s

end

end Work.OddCurve.LowSlope
