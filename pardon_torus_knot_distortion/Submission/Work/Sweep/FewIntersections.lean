import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.SweepCount
import Submission.Work.Sweep.LengthInBallCor
import Submission.Work.Sweep.FewIntersections.volume_pos_of_lintegral_le
import Submission.Work.Sweep.AeTransverseSphere.ae_transverse_sphere

/-!
# Existence of a sphere with few intersections (Deliverable 3)

Combining the coarea formula over the concentric spheres
(`lintegral_sphereCount_le`, which bounds the integral over `r ∈ [R/2, R]` of the
number of intersections by the arclength in the ball) with the length bound for
balls (`arclengthIn_closedBall_le`, which bounds that arclength by `4 d R`), the
integral of the number of intersections is at most `4 d R`, while the interval
`[R/2, R]` has length `R/2`.  Since the count is integer-valued, this forces some
radius `r ∈ [R/2, R]` at which the number of intersections is at most `8 d`.

The same argument applies to the set of radii at which the count is at most `8 d`,
which therefore has *positive measure*; intersecting with the set of full measure
on which the spheres are transverse (Sard, `ae_transverse_sphere`) shows that the
good radius can even be taken transverse.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- **Deliverable 3, measure form.**

For `R > 0` the set of radii `r ∈ [R/2, R]` at which the knot meets the sphere of
radius `r` about `x` in at most `8 d` parameters has positive measure. -/
theorem volume_pos_sphereCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 < R) :
    0 < volume {r ∈ Set.Icc (R / 2) R | sphereCount K x r ≤ ENNReal.ofReal (8 * d)} := by
  have hcoa := lintegral_sphereCount_le K x hR
  have hlen := arclengthIn_closedBall_le hd hbound x (R := R)
  have hint : ∫⁻ r in Set.Icc (R / 2) R, ((sphereParamSet K x r).encard : ENNReal) ≤
      ENNReal.ofReal (4 * d * R) := hcoa.trans hlen
  have hpos := FewIntersections.volume_pos_of_lintegral_le
    (g := fun r => (sphereParamSet K x r).encard) hR hint
  have h8 : 2 * (4 * d * R) / R = 8 * d := by
    field_simp
    ring
  rwa [h8] at hpos

/-- **Deliverable 3, existence of a transverse sphere with few intersections.**

For every point `x` and radius `R > 0` there is `r ∈ [R/2, R]` such that the
sphere of radius `r` about `x` is transverse to the knot and meets it in at most
`8 d` parameters. -/
theorem exists_transverse_sphereCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc (R / 2) R,
      IsTransverseSphere K x r ∧ sphereCount K x r ≤ ENNReal.ofReal (8 * d) := by
  have hvol := volume_pos_sphereCount_le hd hbound x hR
  have hbad : volume {r : ℝ | ¬ IsTransverseSphere K x r} = 0 :=
    MeasureTheory.ae_iff.mp (AeTransverseSphere.ae_transverse_sphere K x)
  by_contra h
  have hsub : {r ∈ Set.Icc (R / 2) R | sphereCount K x r ≤ ENNReal.ofReal (8 * d)} ⊆
      {r : ℝ | ¬ IsTransverseSphere K x r} := by
    intro r hr hT
    exact h ⟨r, hr.1, hT, hr.2⟩
  rw [measure_mono_null hsub hbad] at hvol
  exact lt_irrefl 0 hvol

/-- **Deliverable 3, sphere form (no transversality).**

For every point `x` and radius `R > 0` there is `r ∈ [R/2, R]` such that the knot
meets the sphere of radius `r` about `x` in at most `8 d` parameters. -/
theorem exists_sphereCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc (R / 2) R, sphereCount K x r ≤ ENNReal.ofReal (8 * d) :=
  let ⟨r, hr, _, hc⟩ := exists_transverse_sphereCount_le hd hbound x hR
  ⟨r, hr, hc⟩

/-- **Deliverable 3, counting form.**

The number of intersections can be measured by `Set.ncard`: there is `r ∈ [R/2, R]`
such that the sphere of radius `r` about `x` meets the curve in at most `8 d`
points (and in particular the intersection is finite). -/
theorem exists_sphere_ncard_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Icc (R / 2) R,
      ((sphereParamSet K x r).ncard : ℝ) ≤ 8 * d := by
  obtain ⟨r, hr, hc⟩ := exists_sphereCount_le hd hbound x hR
  refine ⟨r, hr, ?_⟩
  have hfin : (sphereParamSet K x r).Finite := by
    have h1 : ((sphereParamSet K x r).encard : ENNReal) < ⊤ :=
      lt_of_le_of_lt hc ENNReal.ofReal_lt_top
    rw [ENat.toENNReal_lt_top] at h1
    exact Set.encard_lt_top_iff.mp h1
  have h2 : ((sphereParamSet K x r).ncard : ENNReal) ≤ ENNReal.ofReal (8 * d) := by
    rw [show ((sphereParamSet K x r).ncard : ENNReal) =
        ((sphereParamSet K x r).ncard : ℕ∞) from (ENat.toENNReal_coe _).symm,
      hfin.cast_ncard_eq]
    exact hc
  have h3 : ((sphereParamSet K x r).ncard : ℝ) ≤ 8 * d := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this
  exact h3

end Work.Sweep
