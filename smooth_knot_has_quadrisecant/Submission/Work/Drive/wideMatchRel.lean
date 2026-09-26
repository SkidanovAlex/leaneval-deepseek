import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chamferVelBranch
import Submission.Work.Drive.sweepMatchRawVel

/-!
# The matching relation for the raw velocity of the chamfered sweep loop

`Work.Drive.wideMatchRel` is the version of `Work.Drive.sweepMatchRawVel` valid for *all*
sweep parameters `σ ∈ (0,1)` (and chamfer fractions `lam ≤ 1/4`): the raw velocity `chamferVel`
of the chamfered sweep loop differs from the matched knot velocity
`wideRho ... lam (sweepParam τ) • velocity r (wideSig D lam σ τ)` by at most
`M₂ (1 + period) (lam + (period - sweepW' D σ))` times that same matched rate, for any
Lipschitz constant `M₂` of the knot velocity.

The zone estimates of `Submission.Work.Drive.sweepMatchRawVel` (arc / first chamfer / chord /
second chamfer) use *no* hypothesis on `σ` beyond `0 ≤ sweepW' D σ ≤ period`
(`Work.Drive.smv_sweepW'_nonneg_le`, valid for every real `σ`), so the same assembly goes through
on the wider range; the only difference is that the target states the matched parameter as
`Work.Drive.wideSig`, which is definitionally `Work.Drive.topSigma`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

theorem wideMatchRel {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hM₂ : ∀ x y : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r x
        - LeanEval.KnotTheory.Quadrisecant.velocity r y‖ ≤ M₂ * |x - y|)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∀ (σ lam τ : ℝ), 0 < σ → σ < 1 → 0 < lam → lam ≤ 1 / 4 →
      ‖Work.Drive.chamferVel r D lam σ τ -
        Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam
            (Work.Drive.sweepParam τ) •
          LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.wideSig D lam σ τ)‖
        ≤ M₂ * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
            (lam + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) *
          Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam
            (Work.Drive.sweepParam τ) := by
  intro σ lam τ _hσ0 _hσ1 hlam0 hlam14
  have hlam1 : lam < 1 / 2 := by linarith
  -- the two matched phases are the same function
  have hsw : wideSig D lam σ = topSigma D lam σ := rfl
  simp only [hsw]
  obtain ⟨hw0, hwP⟩ := smv_sweepW'_nonneg_le D σ
  have hdd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hddP : period - sweepW' D σ ≤ period := by linarith
  have hρ0 : 0 ≤ M₂ * (1 + period) * (lam + (period - sweepW' D σ)) :=
    mul_nonneg (mul_nonneg hM₂0 (by linarith [period_pos])) (by linarith)
  by_cases h1 : sweepParam τ ≤ 1 / 2
  · rw [smv_arc hr D h1, sub_self, norm_zero]
    refine mul_nonneg hρ0 ?_
    rw [wideRho_arc h1]
    exact mul_nonneg (by linarith)
      (div_nonneg (mul_nonneg (by norm_num) hw0) (le_of_lt period_pos))
  · by_cases h2 : sweepParam τ ≤ 1 / 2 + lam / 2
    · rw [wideRho_chamfer₁ h1 h2]
      exact (smv_cham1 hr hM₂0 hM₂ D hlam0 hlam1 h1 h2).trans
        (smv_arith_cham hM₂0 hlam0 (le_of_lt hlam1) hw0 hwP hdd0 hddP)
    · by_cases h3 : sweepParam τ ≤ 1 - lam / 2
      · exact smv_chord hr hM₂0 hM₂ D hlam0 hlam1 h1 h2 h3
      · rw [wideRho_chamfer₂ h1 h2 h3]
        exact (smv_cham2 hr hM₂0 hM₂ D hlam0 hlam1 h1 h2 h3).trans
          (smv_arith_cham hM₂0 hlam0 (le_of_lt hlam1) hw0 hwP hdd0 hddP)

end Work.Drive
