import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferProfDefs
import Submission.Work.Drive.chamferProfSeparation
import Submission.Work.Drive.chamferProfGen_injOn_of_separation
import Submission.Work.Drive.radialGapOfTools
import Submission.Work.Drive.thinLoopSeparation

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant in
/-- **Lemma A of the lead's uniform-`ρ₀` design** (`NOTES_LEAD_endgameUniform.md` §4): the slices of
the generalised chamfer loop are injective on one period in the zones where the depth `α σ * W` is
an absolute length, from the two radial gaps at the cut points, the two ball bounds for the
connectors, the disjointness of the two connector balls and the no-middle hypothesis on the retained
arc.  Pure geometry: no tilt, no `havoid`, no `hinfl`. -/
theorem chamferLoopGenInjOnBall {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    {lay : ℝ} (hl0 : 0 < lay) (hl : lay < 1 / 2) {α β : ℝ → ℝ} {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (hα : 0 < α σ) (hα2 : 2 * α σ < 1) (hβ : 0 < β σ)
    (hgapA : ∀ θ : ℝ, taR D σ + α σ * sweepW' D σ < θ → θ ≤ tbR D σ - α σ * sweepW' D σ →
      ‖sweepArc' r D σ (α σ) - r (taR D σ)‖ < ‖r θ - r (taR D σ)‖)
    (hgapB : ∀ θ : ℝ, taR D σ + α σ * sweepW' D σ ≤ θ → θ < tbR D σ - α σ * sweepW' D σ →
      ‖sweepArc' r D σ (1 - α σ) - r (tbR D σ)‖ < ‖r θ - r (tbR D σ)‖)
    (hballA : β σ * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ (α σ) - r (taR D σ)‖)
    (hballB : β σ * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ (1 - α σ) - r (tbR D σ)‖)
    (hsum : ‖sweepArc' r D σ (α σ) - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - α σ) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖)
    (hmid : ∀ u : ℝ, taR D σ + α σ * sweepW' D σ ≤ u → u ≤ tbR D σ - α σ * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    Set.InjOn (chamferLoopGen r D lay α β σ) (Set.Ico 0 period) := by
  -- the geometric input: the eight point-set separations of the profile
  have hbeta2 : 2 * β σ < 1 := clg_beta_lt_half D hβ hballA hballB hsum
  have hAB : r (taR D σ) ≠ r (tbR D σ) := clg_AB_ne D hsum
  have harc : Set.InjOn (fun ξ : ℝ => sweepArc' r D σ ξ) (Set.Icc (α σ) (1 - α σ)) :=
    clg_arc_injOn hr D hσ hα hα2
  have hchord : Set.InjOn (fun ξ : ℝ => sweepChord' r D σ ξ) (Set.Icc (β σ) (1 - β σ)) :=
    clg_chord_injOn D hAB
  have hac : ∀ ξ ∈ Set.Icc (α σ) (1 - α σ), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ' :=
    clg_arc_ne_chord D hσ hα hα2 hmid
  have harc_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc (α σ) (1 - α σ),
      (1 - c) • sweepArc' r D σ (1 - α σ) + c • sweepChord' r D σ (1 - β σ)
        = sweepArc' r D σ ξ → ξ = 1 - α σ :=
    clg_arc_head D hσ hβ hgapB hballB
  have harc_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc (α σ) (1 - α σ),
      (1 - c) • sweepChord' r D σ (β σ) + c • sweepArc' r D σ (α σ)
        = sweepArc' r D σ ξ → ξ = α σ :=
    clg_arc_tail D hσ hβ hgapA hballA
  have hchord_tail : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc (β σ) (1 - β σ),
      (1 - c) • sweepChord' r D σ (β σ) + c • sweepArc' r D σ (α σ)
        = sweepChord' r D σ ξ → c = 0 :=
    clg_chord_tail hr D hσ hα hα2 hβ hsum hmid
  have hchord_head : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc (β σ) (1 - β σ),
      (1 - c) • sweepArc' r D σ (1 - α σ) + c • sweepChord' r D σ (1 - β σ)
        = sweepChord' r D σ ξ → c = 1 :=
    clg_chord_head hr D hσ hα hα2 hβ hsum hmid
  have hchamfers : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
      (1 - c) • sweepChord' r D σ (β σ) + c • sweepArc' r D σ (α σ)
        ≠ (1 - c') • sweepArc' r D σ (1 - α σ)
          + c' • sweepChord' r D σ (1 - β σ) :=
    clg_chamfers D hβ hballA hballB hsum
  -- the combinatorial core: the profile is injective on `[0,1)`
  have hprof : Set.InjOn (chamferProfGen r D lay (α σ) (β σ) σ) (Set.Ico (0 : ℝ) 1) :=
    chamferProfGen_injOn_of_separation D hl0 hl hα hα2 hβ hbeta2 harc hchord hac harc_head
      harc_tail hchord_tail hchord_head hchamfers
  -- transfer from the profile to the loop on one period
  intro t₁ ht₁ t₂ ht₂ heq
  rw [chamferLoopGen_eq_prof, chamferLoopGen_eq_prof] at heq
  have hpar : sweepParam t₁ = sweepParam t₂ :=
    hprof (sweepParam_mem t₁) (sweepParam_mem t₂) heq
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at hpar
  have h3 : t₁ / period * period = t₂ / period * period := by rw [hpar]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h3

end Work.Drive
