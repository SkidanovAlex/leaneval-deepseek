import Mathlib
import Submission.Work.Drive.needleProfileDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# The arc side of the needle never meets its chord side

`Work.Drive.chordEndA`/`chordEndB` are the two endpoints of the needle's chord.  Any direction `e`
perpendicular to the chord, evaluated on a *chord-side* point of the needle (a point of the segment
between the two endpoints), gives `0`; evaluated on a point whose *arc-side height*
`⟪N t - chordEndA, e⟫` is positive, it gives that positive number.  Hence such a point is never a
point of the chord segment.

This is the cross-zone half of the injectivity of the needle: it separates the chord zone (where
`Work.Drive.needleChordZoneMono` identifies the needle with the segment) from the arc-side zones
(where `Work.Drive.needleArcZoneMono` and the height analysis of
`Work.Drive.needleFam_inner_eq_devAvg_of_orth` live).
-/

/-- **A point with positive height above the chord's line is not on the chord segment.** -/
theorem ne_chordSegment_of_height_pos {A B P e : Space} (he : inner ℝ e (B - A) = 0)
    {s : ℝ} (h : 0 < inner ℝ (P - A) e) :
    P ≠ (1 - s) • A + s • B := by
  intro hP
  have key : ((1 - s) • A + s • B) - A = s • (B - A) := by
    rw [smul_sub]
    simp only [sub_smul, one_smul]
    abel
  have h0 : inner ℝ (P - A) e = 0 := by
    rw [hP, key, inner_smul_left, real_inner_comm, he, mul_zero]
  linarith

/-- **The cross-zone separation for the needle.**  Let `e` be perpendicular to the needle's chord
`chordEndA chordEndB`.  If the needle's point at `t` has positive height above the chord's line and
the needle's point at `t'` lies on the chord segment, then the two points differ. -/
theorem needleFam_ne_of_chordZone {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ ε t t' : ℝ} {e : Space}
    (he : inner ℝ e (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) = 0)
    (hpos : 0 < inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e)
    {s : ℝ} (hs : needleFam r D lam δ₁ δ₂ ε t'
      = (1 - s) • chordEndA r D δ₂ ε + s • chordEndB r D δ₂ ε) :
    needleFam r D lam δ₁ δ₂ ε t ≠ needleFam r D lam δ₁ δ₂ ε t' := by
  intro hEq
  have h0 : inner ℝ (((1 - s) • chordEndA r D δ₂ ε + s • chordEndB r D δ₂ ε)
      - chordEndA r D δ₂ ε) e = 0 := by
    have key : ((1 - s) • chordEndA r D δ₂ ε + s • chordEndB r D δ₂ ε)
        - chordEndA r D δ₂ ε = s • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := by
      rw [smul_sub]
      simp only [sub_smul, one_smul]
      abel
    rw [key, inner_smul_left, real_inner_comm, he, mul_zero]
  have h0' : inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e = 0 := by
    rw [hEq, hs]
    exact h0
  linarith

end Work.Drive
