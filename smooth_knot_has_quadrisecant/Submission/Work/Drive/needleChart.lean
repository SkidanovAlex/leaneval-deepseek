import Mathlib
import Submission.Work.Drive.sweepFam_chordZone
import Submission.Work.Drive.needleProfileDefs

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-!
# The chart identities of the needle

The two halves of the needle are described by the two zone lemmas of the chord sweep:
`Work.Drive.sweepFam_arcZone` (the arc side is the double `sweepBump`-average of the retained-arc
points, packaged as `Work.Drive.needleFam_arcZone`) and `Work.Drive.sweepFam_chordZone` (the chord
side is the exact straight segment between the two `σ`-blurred endpoints).

This module fixes the *chord-side* interface: the needle on the chord zone is precisely the affine
combination of `chordEndA` and `chordEndB` with the chord parameter
`sweepChordParam lam (sweepParam t)`.  Consequently, in any frame with `e` perpendicular to the
chord, its `e`-coordinate relative to `chordEndA` vanishes identically; that is the `e`-chart
identity the star-shapedness assembly `(D2)` consumes, its arc-side companion being
`Work.Drive.needleFam_inner_eq_devAvg_of_orth`.
-/

/-- **The needle on the chord zone is the straight segment between the two chord endpoints.** -/
theorem needleFam_chordZone {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hclean : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      1 / 2 + lam / 2 ≤ sweepParam (t - δ₁ * u) ∧ sweepParam (t - δ₁ * u) ≤ 1 - lam / 2) :
    needleFam r D lam δ₁ δ₂ ε t
      = (1 - sweepChordParam lam (sweepParam t)) • chordEndA r D δ₂ ε
        + sweepChordParam lam (sweepParam t) • chordEndB r D δ₂ ε := by
  simpa only [needleFam, chordEndA, chordEndB] using
    sweepFam_chordZone (r := r) hr D (σ := ε) hlam0 hlam1 hclean

/-- **The `e`-chart identity on the chord zone**: the needle's `e`-coordinate relative to
`chordEndA` vanishes, for every `e` perpendicular to the chord. -/
theorem needleFam_chordZone_inner {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hclean : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      1 / 2 + lam / 2 ≤ sweepParam (t - δ₁ * u) ∧ sweepParam (t - δ₁ * u) ≤ 1 - lam / 2)
    {e : Space} (he : inner ℝ e (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) = 0) :
    inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e = 0 := by
  rw [needleFam_chordZone hr D hlam0 hlam1 hclean]
  have hBA : inner ℝ (chordEndB r D δ₂ ε) e = inner ℝ (chordEndA r D δ₂ ε) e := by
    have h : inner ℝ e (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) = 0 := he
    rw [inner_sub_right] at h
    have h' : inner ℝ e (chordEndB r D δ₂ ε) = inner ℝ e (chordEndA r D δ₂ ε) := by linarith [h]
    have h₂ : inner ℝ (chordEndB r D δ₂ ε) e = inner ℝ e (chordEndB r D δ₂ ε) := real_inner_comm _ _
    have h₃ : inner ℝ (chordEndA r D δ₂ ε) e = inner ℝ e (chordEndA r D δ₂ ε) := real_inner_comm _ _
    rw [h₂, h₃]
    exact h'
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hBA]
  ring

end Work.Drive
