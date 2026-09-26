import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.LevelCount
import Submission.Work.Sweep.Coarea
import Submission.Work.Sweep.LengthInBallCor
import Submission.Work.Sweep.SweepCount
import Submission.Work.Sweep.SweepCountCoord
import Submission.Work.Sweep.FewIntersections
import Submission.Work.Sweep.FewIntersectionsCoord
import Submission.Work.Sweep.AeTransverseSphere.ae_transverse_sphere
import Submission.Work.Sweep.AeTransverseCoord.ae_transverse_coord
import Submission.Work.Sweep.AeFiniteSphere.ae_finite_sphereParamSet
import Submission.Work.Sweep.AeFiniteCoord.ae_finite_coordParamSet

/-!
# Integral geometry of a sweep: summary of the interface

This module collects the main results of the `Work.Sweep` subproject, the
integral-geometric estimates used in Pardon's proof of the torus-knot distortion
bound.  Import this file to get everything.

## Definitions (`Submission/Work/Sweep/Defs.lean`)

* `Work.Sweep.IsDistortionBound K d` — `d` bounds the ratio of intrinsic to
  Euclidean distance on the fundamental interval.
* `Work.Sweep.arclengthIn K E` — the arclength of the portion of the curve over
  the parameter set `E`, as `ℝ≥0∞` (the Lebesgue integral of the speed over `E`).
* `Work.Sweep.paramSetIn K B` / `paramSetInIco K B` — parameters of `[0, 2π]` /
  `[0, 2π)` whose image lies in `B`.
* `Work.Sweep.sphereParamSet K x r`, `sphereParamSetIco K x r`,
  `Work.Sweep.sphereCount K x r` — parameters at which the curve meets the sphere
  of radius `r` about `x`, and their (extended) number.
* `Work.Sweep.coordParamSet K x R s`, `Work.Sweep.coordCount K x R s` — the same
  for the plane `{y | y 2 = s}` cut out by the ball of radius `R`.
* `Work.Sweep.IsTransverseSphere`, `Work.Sweep.IsTransverseCoord` — the curve is
  not tangent to the sphere, respectively the plane.

## Main results

* **Length bound (Deliverable 1).**
  `Work.Sweep.arclengthIn_closedBall_le` and `Work.Sweep.arclengthIn_ball_le`:
  the arclength of the part of the curve inside a ball of radius `R` is at most
  `4 d R`; `Work.Sweep.arclengthIn_paramSetIn_le_of_diam` is the general form for
  a set of diameter `D` (the underlying lemma, stated for `[0, 2π)`, is
  `Work.Sweep.LengthInBall.arclengthIn_le_of_diam`).
* **Coarea formula (Deliverable 2).**
  `Work.Sweep.lintegral_sphereCount_le`: the integral over `r ∈ [R/2, R]` of the
  number of intersections with the sphere of radius `r` is at most the arclength
  of the part of the curve in the closed ball of radius `R`; and
  `Work.Sweep.lintegral_coordCount_le`: the same estimate for the levels of the
  third coordinate.  The abstract one-dimensional coarea inequality behind them is
  `Work.Sweep.lintegral_mul_levelCount_le_subset`.
* **Few intersections (Deliverable 3).**
  `Work.Sweep.exists_sphereCount_le`, `Work.Sweep.exists_transverse_sphereCount_le`,
  `Work.Sweep.exists_sphere_ncard_le`, `Work.Sweep.exists_transverse_sphereIco_ncard_le`
  and the packaged `Work.Sweep.exists_good_sphere`; the positive-measure form is
  `Work.Sweep.volume_pos_sphereCount_le`.  For planes: `Work.Sweep.exists_coordCount_le`,
  `Work.Sweep.exists_transverse_coordCount_le`.
* **Transversality (Deliverable 4).**
  `Work.Sweep.AeTransverseSphere.ae_transverse_sphere`,
  `Work.Sweep.AeTransverseCoord.ae_transverse_coord`: a.e. radius, respectively
  level, is transverse; `Work.Sweep.AeFiniteSphere.ae_finite_sphereParamSet`,
  `Work.Sweep.AeFiniteCoord.ae_finite_coordParamSet`: the intersections are finite
  for a.e. radius, respectively level.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

lemma sphereParamSetIco_subset (K : Knot) (x : R3) (r : ℝ) :
    sphereParamSetIco K x r ⊆ sphereParamSet K x r :=
  Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self

/-- A.e. finiteness of the intersections for the half-open fundamental interval,
as requested by the phrasing with `[0, 2π)`. -/
theorem ae_finite_sphereParamSetIco (K : Knot) (x : R3) :
    ∀ᵐ r ∂volume, (sphereParamSetIco K x r).Finite :=
  (AeFiniteSphere.ae_finite_sphereParamSet K x).mono fun _ h =>
    h.subset (sphereParamSetIco_subset K x _)

lemma ncard_sphereParamSetIco_le (K : Knot) (x : R3) (r : ℝ)
    (h : (sphereParamSet K x r).Finite) :
    (sphereParamSetIco K x r).ncard ≤ (sphereParamSet K x r).ncard :=
  Set.ncard_le_ncard (sphereParamSetIco_subset K x r) h

/-- If the (extended) number of intersections with a sphere is bounded by a real
number, then it is finite and the honest `ncard` satisfies the same bound. -/
lemma ncard_le_of_sphereCount_le {K : Knot} {x : R3} {r c : ℝ} (hc0 : 0 ≤ c)
    (hc : sphereCount K x r ≤ ENNReal.ofReal c) :
    ((sphereParamSet K x r).ncard : ℝ) ≤ c := by
  have hfin : (sphereParamSet K x r).Finite := by
    have h1 : ((sphereParamSet K x r).encard : ENNReal) < ⊤ :=
      lt_of_le_of_lt hc ENNReal.ofReal_lt_top
    rw [ENat.toENNReal_lt_top] at h1
    exact Set.encard_lt_top_iff.mp h1
  have h3 : ((sphereParamSet K x r).ncard : ENNReal) ≤ ENNReal.ofReal c := by
    rw [show ((sphereParamSet K x r).ncard : ENNReal) =
        ((sphereParamSet K x r).ncard : ℕ∞) from (ENat.toENNReal_coe _).symm,
      hfin.cast_ncard_eq]
    exact hc
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
  rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hc0] at this

/-- **Deliverable 3, form with the half-open fundamental interval `[0, 2π)`.**

There exists a transverse sphere of radius `r ∈ [R/2, R]` meeting the curve in at
most `8 d` points, counted with parameters in `[0, 2π)`. -/
theorem exists_transverse_sphereIco_ncard_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc (R / 2) R, IsTransverseSphere K x r ∧
      ((sphereParamSetIco K x r).ncard : ℝ) ≤ 8 * d := by
  obtain ⟨r, hr, hT, hc⟩ := exists_transverse_sphereCount_le hd hbound x hR
  have hfin : (sphereParamSet K x r).Finite := by
    have h1 : ((sphereParamSet K x r).encard : ENNReal) < ⊤ :=
      lt_of_le_of_lt hc ENNReal.ofReal_lt_top
    rw [ENat.toENNReal_lt_top] at h1
    exact Set.encard_lt_top_iff.mp h1
  refine ⟨r, hr, hT, ?_⟩
  calc ((sphereParamSetIco K x r).ncard : ℝ)
      ≤ ((sphereParamSet K x r).ncard : ℝ) := by
        exact_mod_cast ncard_sphereParamSetIco_le K x r hfin
    _ ≤ 8 * d := ncard_le_of_sphereCount_le (by positivity) hc

/-- **The sweep estimate for spheres, combined form.**

For every point `x`, radius `R > 0` and distortion bound `d` of `K` there is
`r ∈ [R/2, R]` such that the sphere of radius `r` about `x` is transverse to the
curve, meets it in finitely many points, and meets it in at most `8 d` points of
the fundamental interval `[0, 2π)`. -/
theorem exists_good_sphere {K : Knot} {d : ℝ} (hd : 0 ≤ d) (hbound : IsDistortionBound K d)
    (x : R3) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc (R / 2) R, IsTransverseSphere K x r ∧
      (sphereParamSet K x r).Finite ∧ ((sphereParamSetIco K x r).ncard : ℝ) ≤ 8 * d := by
  obtain ⟨r, hr, hT, hc⟩ := exists_transverse_sphereCount_le hd hbound x hR
  have hfin : (sphereParamSet K x r).Finite := by
    have h1 : ((sphereParamSet K x r).encard : ENNReal) < ⊤ :=
      lt_of_le_of_lt hc ENNReal.ofReal_lt_top
    rw [ENat.toENNReal_lt_top] at h1
    exact Set.encard_lt_top_iff.mp h1
  have h2 : ((sphereParamSetIco K x r).ncard : ℝ) ≤ 8 * d := by
    calc ((sphereParamSetIco K x r).ncard : ℝ)
        ≤ ((sphereParamSet K x r).ncard : ℝ) := by
          exact_mod_cast ncard_sphereParamSetIco_le K x r hfin
      _ ≤ 8 * d := ncard_le_of_sphereCount_le (by positivity) hc
  exact ⟨r, hr, hT, hfin, h2⟩

end Work.Sweep
