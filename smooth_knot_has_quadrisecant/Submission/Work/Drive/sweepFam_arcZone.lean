import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepBlurFacts

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- **The chamfered loop on its arc zone.**  If the loop fraction `sweepParam t ≤ 1/2` the loop is
on its arc side, i.e. the retained arc of the knot traversed from fraction `ξ = lam` to
`ξ = 1 - lam` as `sweepParam t` runs from `0` to `1/2`. -/
lemma sweepLoopChamfer_arcZone {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s t : ℝ} (h : sweepParam t ≤ 1 / 2) :
    sweepLoopChamfer r D lam s t
      = sweepArc' r D s (lam + (1 - 2 * lam) * (2 * sweepParam t)) := by
  simp only [sweepLoopChamfer]
  rw [if_pos h]

theorem sweepFam_arcZone {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : Continuous r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ σ t : ℝ} (hlam1 : lam < 1 / 2)
    (hclean : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        Work.Drive.sweepParam (t - δ₁ * u) ≤ 1 / 2) :
    Work.Drive.sweepFam r D lam δ₁ δ₂ σ t
      = ∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
          (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u •
            r (Work.Drive.taR D (σ - δ₂ * v) +
              (lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (t - δ₁ * u))) *
                Work.Drive.sweepW' D (σ - δ₂ * v))) := by
  -- The loop-parameter window lies entirely on the arc side, so the loop-parameter convolution
  -- collapses to the retained-arc point at fraction `lam + (1 - 2*lam) * (2 * sweepParam ·)`.
  have hinner : ∀ s : ℝ, sweepSmoothT r D lam δ₁ s t
      = ∫ u in (-1 : ℝ)..1, sweepBump u •
          r (taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam (t - δ₁ * u))) * sweepW' D s) := by
    intro s
    simp only [sweepSmoothT]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    rw [sweepLoopChamfer_arcZone D (hclean u hu), sweepArc']
  -- The sweep-parameter convolution only moves the sweep parameter of the arc point.
  simp only [sweepFam]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  rw [hinner (σ - δ₂ * v)]

end Work.Drive
