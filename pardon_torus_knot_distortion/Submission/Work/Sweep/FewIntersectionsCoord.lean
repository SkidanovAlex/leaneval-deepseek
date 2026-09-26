import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.SweepCountCoord
import Submission.Work.Sweep.LengthInBallCor
import Submission.Work.Sweep.FewIntersectionsGen.volume_pos_of_lintegral_le_Icc
import Submission.Work.Sweep.AeTransverseCoord.ae_transverse_coord

/-!
# Existence of a coordinate level with few intersections (Deliverable 3)

The companion of `FewIntersections.lean` for the family of coordinate planes: the
coarea formula over the planes `{y | y 2 = s}` (`lintegral_coordCount_le`) bounds
the integral over `s ∈ [-ε, ε]` of the number of intersections inside the ball by
the arclength in the ball, which is at most `4 d R`.  Since the interval has
length `2ε`, some level `s ∈ [-ε, ε]` gives at most `2 d R / ε` intersections, and
(as for the spheres) the level can be taken transverse.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- **Deliverable 3 for coordinate planes, measure form.** -/
theorem volume_pos_coordCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    0 < volume {s ∈ Set.Icc (-ε) ε | coordCount K x R s ≤ ENNReal.ofReal (2 * d * R / ε)} := by
  have hcoa := lintegral_coordCount_le K x R ε
  have hlen := arclengthIn_ball_le hd hbound x (R := R)
  have hint : ∫⁻ s in Set.Icc (-ε) ε, ((coordParamSet K x R s).encard : ENNReal) ≤
      ENNReal.ofReal (4 * d * R) := hcoa.trans hlen
  have hpos := FewIntersectionsGen.volume_pos_of_lintegral_le_Icc (a := -ε) (b := ε)
    (C := 4 * d * R) (g := fun s => (coordParamSet K x R s).encard) (by linarith) hint
  have h2 : 4 * d * R / (ε - -ε) = 2 * d * R / ε := by
    field_simp
    ring
  rwa [h2] at hpos

/-- **Deliverable 3 for coordinate planes, transversality form.**

For every `x`, `R > 0` and `ε > 0` there is `s ∈ [-ε, ε]` such that the plane
`{y | y 2 = s}` is transverse to the knot, and meets the part of the knot inside
the ball of radius `R` about `x` in at most `2 d R / ε` parameters. -/
theorem exists_transverse_coordCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ s ∈ Set.Icc (-ε) ε, IsTransverseCoord K x R s ∧
      coordCount K x R s ≤ ENNReal.ofReal (2 * d * R / ε) := by
  have hvol := volume_pos_coordCount_le hd hbound x (R := R) (ε := ε) hR hε
  have hbad : volume {s : ℝ | ¬ IsTransverseCoord K x R s} = 0 :=
    MeasureTheory.ae_iff.mp (AeTransverseCoord.ae_transverse_coord K x R)
  by_contra h
  have hsub : {s ∈ Set.Icc (-ε) ε | coordCount K x R s ≤ ENNReal.ofReal (2 * d * R / ε)} ⊆
      {s : ℝ | ¬ IsTransverseCoord K x R s} := by
    intro s hs hT
    exact h ⟨s, hs.1, hT, hs.2⟩
  rw [measure_mono_null hsub hbad] at hvol
  exact lt_irrefl 0 hvol

/-- **Deliverable 3 for coordinate planes (no transversality).** -/
theorem exists_coordCount_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ s ∈ Set.Icc (-ε) ε, coordCount K x R s ≤ ENNReal.ofReal (2 * d * R / ε) :=
  let ⟨s, hs, _, hc⟩ := exists_transverse_coordCount_le hd hbound x hR hε
  ⟨s, hs, hc⟩

end Work.Sweep
