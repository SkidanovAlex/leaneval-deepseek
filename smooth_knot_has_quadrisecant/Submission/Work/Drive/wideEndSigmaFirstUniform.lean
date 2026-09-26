import Mathlib
import Submission.Work.Drive.ofatTopEndDefs
import Submission.Work.Drive.wideEndGivenC
import Submission.Work.Drive.sweepToNeedleEpsOfSlices_gen

/-!
# The wide-end estimate: free constant, and the slice chosen first

`Work.Drive.WideEndUniform` (from `Drive/ofatTopEndDefs.lean`) is the form of the wide-end estimate
that the `OFat` top end consumes.  It is the **merge** of the two wide-end theorems already in the
workspace:

* `Work.Drive.wideEndPrescribedGen_sigmaFirst` (`Drive/sweepToNeedleEpsOfSlices_gen.lean`) fixes the
  trough slice `σ₀` *before* the layout `lay` and the widths — the order the top end needs — but
  returns one *opaque* constant `C` (quantified *after* `ρ₀, δs, cQ`);
* `Work.Drive.wideEndGivenC` (`Drive/wideEndGivenC.lean`, and its copy
  `Work.Drive.wideEndPrescribedGenAt`) frees the constant (`∀ C ≥ Cmin`) but takes the slice `σ₀` as
  an *input* and, as written, returns `Cmin` only *after* `lay, ρ₀, cQ`.

This module proves the merge: a single `Cmin`, independent of `lay`, `ρ₀`, `cQ` (it is the explicit
expression `16 (M₂+1) (1+period) + 16 (Cv+1) (1+period)² + 1` built from the two global bounds of
the knot), and for every `C ≥ Cmin` and every tolerance `ε₁ ≤ C` a slice `σ₀ ∈ (1/2,1)`, chosen from
`ε₁` and `C` **alone**, whose gap is small enough (`C * (period - sweepW' D σ₀) ≤ ε₁/4`) that every
admissible layout `lay ≤ ε₁/(4C)` and every pair `(ρ₀, cQ)` gets the estimate with tolerance `ε₁`.

The proof is the transcription of `wideEndPrescribedGen`'s estimate with the budget bookkeeping
re-done: the constant is not chosen but assumed `≥ Cmin` (so that `hCa`, `hCb` still give the two
`16 (…)` bounds), the slice is chosen from the modulus of continuity of `σ ↦ sweepW' D σ` at `1`
with tolerance `ε₁/(8C)`, and the layout enters only through `C * lay ≤ ε₁/4`.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

theorem wideEndSigmaFirstUniform {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) {δs : ℝ}
    (hδs : 0 < δs) : Work.Drive.WideEndUniform r D δs := by
  obtain ⟨M₀, M₁, M₂, hM₀0, hM₁0, hM₂0, hM₀, hM₁, hM₂⟩ := exists_knot_bounds hr
  obtain ⟨Cv, hCv0, hval0⟩ := wideendRawPos (r := r) (M₁ := M₁) (M₂ := M₂) hr D hM₁ hM₂
  have hval : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ ≤ 1 →
      ‖sweepLoopChamfer r D lam' σ τ - r (wideSig D lam' σ τ)‖
        ≤ Cv * (lam' * period + (period - sweepW' D σ)) ^ 2 := by
    intro lam' σ τ h1 h2 h3 h4
    exact hval0 σ lam' τ h1 h2 h4
  have hvel : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ < 1 →
      ‖chamferVel r D lam' σ τ - wideRho (sweepW' D σ) (period - sweepW' D σ) lam' (sweepParam τ) •
        velocity r (wideSig D lam' σ τ)‖
        ≤ M₂ * (1 + period) * (lam' + (period - sweepW' D σ)) *
          wideRho (sweepW' D σ) (period - sweepW' D σ) lam' (sweepParam τ) := by
    intro lam' σ τ h1 h2 h3 h4
    exact wideMatchRel hr hM₂0.le hM₂ D σ lam' τ h3 h4 h1 h2
  set Cmin : ℝ := 16 * (M₂ + 1) * (1 + period) + 16 * (Cv + 1) * (1 + period) ^ 2 + 1
    with hCmindef
  have hCminpos : 0 < Cmin := by
    rw [hCmindef]
    nlinarith [hM₂0, hCv0, period_pos]
  have hCmina : 16 * (M₂ + 1) * (1 + period) ≤ Cmin := by
    rw [hCmindef]
    nlinarith [hM₂0, hCv0, period_pos]
  have hCminb : 16 * (Cv + 1) * (1 + period) ^ 2 ≤ Cmin := by
    rw [hCmindef]
    nlinarith [hM₂0, hCv0, period_pos]
  refine ⟨Cmin, hCminpos, ?_⟩
  intro C hCge ε₁ hε₁0 hε₁C
  have hCpos : 0 < C := lt_of_lt_of_le hCminpos hCge
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hCa : 16 * (M₂ + 1) * (1 + period) ≤ C := le_trans hCmina hCge
  have hCb : 16 * (Cv + 1) * (1 + period) ^ 2 ≤ C := le_trans hCminb hCge
  -- ## the trough slice `σ₀`, a function of `ε₁` and `C` alone
  have htolw : 0 < ε₁ / (8 * C) := by positivity
  obtain ⟨δw, hδw0, hδw'⟩ :=
    Metric.continuous_iff.mp (sweepW'_continuous D) 1 (ε₁ / (8 * C)) htolw
  have htol2 : 0 < min (period / 2) (δs / 8) :=
    lt_min (half_pos period_pos) (by linarith [hδs])
  obtain ⟨δw2, hδw20, hδw2'⟩ :=
    Metric.continuous_iff.mp (sweepW'_continuous D) 1 (min (period / 2) (δs / 8)) htol2
  set s : ℝ := min δw (min δw2 (1 / 4)) with hsdef
  have hs0 : 0 < s := lt_min hδw0 (lt_min hδw20 (by norm_num))
  have hsδw : s ≤ δw := min_le_left _ _
  have hsδw2 : s ≤ δw2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs4 : s ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set σ₀ : ℝ := 1 - s / 2 with hσ₀def
  have hσ₀0 : 0 < σ₀ := by rw [hσ₀def]; linarith
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀def]; linarith
  have hσ₀half : 1 / 2 < σ₀ := by rw [hσ₀def]; linarith
  have hW1 : sweepW' D 1 = period := sweepW'_eq_period_of_one_le D le_rfl
  have hdist : dist σ₀ 1 < δw := by
    rw [Real.dist_eq, hσ₀def]
    have h1 : |1 - s / 2 - 1| = s / 2 := by
      rw [show (1 - s / 2 - 1) = -(s / 2) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [h1]; linarith
  have hd : period - sweepW' D σ₀ < ε₁ / (8 * C) := by
    have h := hδw' σ₀ hdist
    rw [Real.dist_eq, hW1] at h
    have hle : sweepW' D σ₀ ≤ period := (sweepW'_nonneg_le D σ₀).2
    have h2 : period - sweepW' D σ₀ = |sweepW' D σ₀ - period| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [h2]; exact h
  have hgap : C * (period - sweepW' D σ₀) ≤ ε₁ / 4 := by
    have h1 := mul_lt_mul_of_pos_left hd hCpos
    have h2 : C * (ε₁ / (8 * C)) = ε₁ / 8 := by
      field_simp
    rw [h2] at h1
    linarith
  refine ⟨σ₀, hσ₀half, hσ₀1, hgap, ?_⟩
  intro lay hlay0 hlay4 hlayC ρ₀ cQ hρ₀ hcQ L hL
  have hd0 : 0 < period - sweepW' D σ₀ := sub_pos.mpr (sweepW'_lt_period D hσ₀1)
  have hlamd : lay + (period - sweepW' D σ₀) ≤ ε₁ / C := by
    rw [le_div_iff₀ hCpos]
    have h1 : C * lay ≤ ε₁ / 4 := hlayC
    have h2 : C * (period - sweepW' D σ₀) ≤ ε₁ / 4 := hgap
    nlinarith [h1, h2, hε₁0]
  -- the two fine-regime conditions
  have hxC : ε₁ / C ≤ 1 := by
    rw [div_le_one hCpos]
    exact hε₁C
  have hx0 : 0 ≤ ε₁ / C := div_nonneg hε₁0.le hCpos.le
  have hx2 : (ε₁ / C) ^ 2 ≤ ε₁ / C := by nlinarith [hx0, hxC]
  have hdC : lay * period + (period - sweepW' D σ₀) ≤ (1 + period) * (ε₁ / C) := by
    have hper1 : (1 : ℝ) ≤ period := by rw [period]; linarith [Real.pi_gt_three]
    nlinarith [hlamd, hper1, hlay0, hd0]
  have hCv1 : (0 : ℝ) ≤ 16 * (Cv + 1) := by linarith
  have hM21 : (0 : ℝ) ≤ 16 * (M₂ + 1) * (1 + period) := by
    have := period_pos; nlinarith [hM₂0]
  have hvalε : 16 * (Cv + 1) * (lay * period + (period - sweepW' D σ₀)) ^ 2 ≤ ε₁ := by
    have hnn : 0 ≤ lay * period + (period - sweepW' D σ₀) := by
      have h := mul_nonneg hlay0.le period_pos.le; linarith [hd0]
    have h2 : (lay * period + (period - sweepW' D σ₀)) ^ 2 ≤ ((1 + period) * (ε₁ / C)) ^ 2 :=
      by nlinarith [hnn, hdC]
    have h4 : 16 * (Cv + 1) * ((1 + period) * (ε₁ / C)) ^ 2
        ≤ 16 * (Cv + 1) * ((1 + period) ^ 2 * (ε₁ / C)) := by
      have hsq : ((1 + period) * (ε₁ / C)) ^ 2 = (1 + period) ^ 2 * (ε₁ / C) ^ 2 := by ring
      rw [hsq]
      have h5 : (1 + period) ^ 2 * (ε₁ / C) ^ 2 ≤ (1 + period) ^ 2 * (ε₁ / C) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
      exact mul_le_mul_of_nonneg_left h5 hCv1
    have h6 : 16 * (Cv + 1) * ((1 + period) ^ 2 * (ε₁ / C)) ≤ ε₁ := by
      have h8 : 16 * (Cv + 1) * ((1 + period) ^ 2 * (ε₁ / C))
          = (16 * (Cv + 1) * (1 + period) ^ 2) * (ε₁ / C) := by ring
      rw [h8]
      calc (16 * (Cv + 1) * (1 + period) ^ 2) * (ε₁ / C)
          ≤ C * (ε₁ / C) := mul_le_mul_of_nonneg_right hCb hx0
        _ = ε₁ := mul_div_cancel₀ ε₁ hCne
    linarith [mul_le_mul_of_nonneg_left h2 hCv1, h4, h6]
  have hvelε : 16 * (M₂ + 1) * (1 + period) * (lay + (period - sweepW' D σ₀)) ≤ ε₁ := by
    have h8 : 16 * (M₂ + 1) * (1 + period) * (lay + (period - sweepW' D σ₀))
        = (16 * (M₂ + 1) * (1 + period)) * (lay + (period - sweepW' D σ₀)) := by ring
    rw [h8]
    calc (16 * (M₂ + 1) * (1 + period)) * (lay + (period - sweepW' D σ₀))
        ≤ (16 * (M₂ + 1) * (1 + period)) * (ε₁ / C) := mul_le_mul_of_nonneg_left hlamd hM21
      _ ≤ C * (ε₁ / C) := mul_le_mul_of_nonneg_right hCa hx0
      _ = ε₁ := mul_div_cancel₀ ε₁ hCne
  -- the width budget: `min L (s/4)`, so that the widths live inside the trough window of `σ₀`
  set Lw : ℝ := min L (s / 4) with hLwdef
  have hLw0 : 0 < Lw := lt_min hL (by linarith)
  have hLwL : Lw ≤ L := min_le_left _ _
  have hLws : Lw ≤ s / 4 := min_le_right _ _
  obtain ⟨δ₁, δ₂, ψ, hδ₁0, hδ₁Lw, hδ₂0, hδ₂Lw, hψsm, hψsh, hψpos, hψ1, hψ2⟩ :=
    widePhaseFormBudget hr D hM₁ hM₂0.le hM₂ hCv0.le hσ₀0 hσ₀1 (wideSig_tau_lipschitz D)
      (wideSig_sigma_modulus D σ₀) hval hvel hε₁0 hLw0 hlay0 hlay4 hvalε hvelε
  have hδ₁L : δ₁ ≤ L := le_trans hδ₁Lw hLwL
  have hδ₂L : δ₂ ≤ L := le_trans hδ₂Lw hLwL
  have hδ₂s : δ₂ ≤ s / 4 := le_trans hδ₂Lw hLws
  -- the schedule is constantly `lay` on the whole blur window of `σ₀`
  have hwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      schedAlpha lay ρ₀ δs D (σ₀ - δ₂ * v) = lay ∧
        schedBeta r lay ρ₀ δs cQ D (σ₀ - δ₂ * v) = lay := by
    intro v hv
    have hvabs : |v| ≤ 1 := by
      rw [Set.mem_Icc] at hv
      exact abs_le.mpr ⟨hv.1, hv.2⟩
    have hdistv : dist (σ₀ - δ₂ * v) 1 < δw2 := by
      have hA : dist (σ₀ - δ₂ * v) σ₀ = |δ₂ * v| := by
        rw [Real.dist_eq, show σ₀ - δ₂ * v - σ₀ = -(δ₂ * v) by ring, abs_neg]
      have hB : dist σ₀ 1 = s / 2 := by
        rw [Real.dist_eq, hσ₀def,
          show 1 - s / 2 - 1 = -(s / 2) by ring, abs_neg,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ s / 2)]
      have hC : |δ₂ * v| ≤ δ₂ := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hδ₂0)]
        nlinarith [hvabs, hδ₂0.le]
      calc dist (σ₀ - δ₂ * v) 1 ≤ dist (σ₀ - δ₂ * v) σ₀ + dist σ₀ 1 := dist_triangle _ _ _
        _ = |δ₂ * v| + s / 2 := by rw [hA, hB]
        _ ≤ δ₂ + s / 2 := by linarith
        _ ≤ s / 4 + s / 2 := by linarith
        _ = 3 * s / 4 := by ring
        _ < s := by linarith
        _ ≤ δw2 := hsδw2
    have hWv := hδw2' (σ₀ - δ₂ * v) hdistv
    rw [Real.dist_eq, hW1] at hWv
    have hWle : sweepW' D (σ₀ - δ₂ * v) ≤ period := (sweepW'_nonneg_le D _).2
    have hWpos : 0 < sweepW' D (σ₀ - δ₂ * v) := by
      have h1 : -(min (period / 2) (δs / 8)) < sweepW' D (σ₀ - δ₂ * v) - period :=
        (abs_lt.mp hWv).1
      have h2 : min (period / 2) (δs / 8) ≤ period / 2 := min_le_left _ _
      have hp : 0 < period := period_pos
      linarith
    have hWne : sweepW' D (σ₀ - δ₂ * v) ≠ 0 := ne_of_gt hWpos
    have hW0 : 0 ≤ sweepW' D (σ₀ - δ₂ * v) := le_of_lt hWpos
    have hc : schedC D (σ₀ - δ₂ * v) ≤ δs / 4 := by
      rw [schedC]
      have hmin2 : min (period / 2) (δs / 8) < δs / 4 := by
        have := min_le_right (period / 2) (δs / 8)
        linarith
      have hsub : period - sweepW' D (σ₀ - δ₂ * v) = |sweepW' D (σ₀ - δ₂ * v) - period| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have hlt : period - sweepW' D (σ₀ - δ₂ * v) < min (period / 2) (δs / 8) := by
        rw [hsub]; exact hWv
      exact le_trans (min_le_right _ _) (le_trans hlt.le hmin2.le)
    exact ⟨schedAlpha_trough D hδs hlay0 hWne hW0 hc, schedBeta_trough D hδs hc⟩
  have hEq := sweepFamOf_chamferLoopGen_eq_sweepFam (r := r) (D := D) (lay := lay)
    (α := schedAlpha lay ρ₀ δs D) (β := schedBeta r lay ρ₀ δs cQ D) (σ := σ₀) (δ₁ := δ₁)
    (δ₂ := δ₂) hwin
  obtain ⟨Θ, hΘsm, hΘsh, hΘpos, hΘ1, hΘ2⟩ :=
    reparamOfPhase (r := r) (Φ := fun u : ℝ => sweepFam r D lay δ₁ δ₂ σ₀ u)
      hψsm hψsh hψpos hε₁0
      ((sweepFam_contDiff_periodic hr.continuous D lay δ₁ δ₂ (ne_of_gt hδ₁0)
        (ne_of_gt hδ₂0)).2.2 σ₀) hψ1 hψ2
  exact ⟨δ₁, δ₂, 0, Θ, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hΘsm, hΘsh,
    hΘpos, fun t => by simpa [hEq] using hΘ1 t, fun t => by simpa [hEq] using hΘ2 t⟩

end Work.Drive
