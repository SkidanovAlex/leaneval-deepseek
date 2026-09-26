import Mathlib
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.wideEndPrescribed
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.widePhaseFormBudget

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real

/-- **The wide-end estimate at a prescribed chamfer fraction, for the scheduled loop.**

This is `Work.Drive.wideEnd_prescribed` with the *scheduled* chamfer loop
`Work.Drive.chamferLoopGen r D lay (schedAlpha …) (schedBeta …)` in place of the standard chamfered
loop `sweepLoopChamfer r D lay`.  The slice used is a *trough* slice of the schedule (`σ₀` close to
`1`, so `schedC D σ ≤ δs/4` and both ramps vanish on the whole blur window), where the schedule is
constantly `lay` and the blurred scheduled family coincides with `sweepFam r D lay δ₁ δ₂`. -/
theorem wideEndPrescribedGen {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lay ρ₀ δs cQ : ℝ} (hlay0 : 0 < lay) (hlay4 : lay ≤ 1 / 4) (hδs : 0 < δs) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ C → 2 * C * lay ≤ ε₁ → ∀ L : ℝ, 0 < L →
      ∃ (σ₀ δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
        1 / 2 < σ₀ ∧ σ₀ < 1 ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
        C * (lay + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ≤ ε₁ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
        (∀ t : ℝ, Θ (t + LeanEval.KnotTheory.Quadrisecant.period)
          = Θ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
        (∀ t : ℝ, 0 < deriv Θ t) ∧
        (∀ t : ℝ, ‖Work.Drive.sweepFamOf
            (Work.Drive.chamferLoopGen r D lay (Work.Drive.schedAlpha lay ρ₀ δs D)
              (Work.Drive.schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ t)
          - r (t + c)‖ < ε₁) ∧
        (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFamOf
            (Work.Drive.chamferLoopGen r D lay (Work.Drive.schedAlpha lay ρ₀ δs D)
              (Work.Drive.schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ u)) t
          - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁) := by
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
  set C : ℝ := 16 * (M₂ + 1) * (1 + period) + 16 * (Cv + 1) * (1 + period) ^ 2 + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    nlinarith [hM₂0, hCv0, period_pos]
  have hCa : 16 * (M₂ + 1) * (1 + period) ≤ C := by
    rw [hCdef]
    nlinarith [hM₂0, hCv0, period_pos]
  have hCb : 16 * (Cv + 1) * (1 + period) ^ 2 ≤ C := by
    rw [hCdef]
    nlinarith [hM₂0, hCv0, period_pos]
  refine ⟨C, hCpos, ?_⟩
  intro ε₁ hε₁0 hε₁C h2Clam L hL
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hε2C : 0 < ε₁ / (2 * C) := div_pos hε₁0 (by positivity)
  have hlayHalf : lay ≤ ε₁ / (2 * C) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
    nlinarith [h2Clam]
  -- a sweep parameter near `1` whose gap `period - W` is below `ε₁/(2C)`
  obtain ⟨δw, hδw, hδw'⟩ := Metric.continuous_iff.mp (sweepW'_continuous D) 1 (ε₁ / (2 * C)) hε2C
  -- and a neighbourhood of `1` on which `period - W` is below `δs/4` (and `W > 0`)
  have htol2 : 0 < min (period / 2) (δs / 8) :=
    lt_min (half_pos period_pos) (by linarith [hδs])
  obtain ⟨δw2, hδw20, hδw2'⟩ :=
    Metric.continuous_iff.mp (sweepW'_continuous D) 1 (min (period / 2) (δs / 8)) htol2
  set s : ℝ := min δw (min δw2 (1 / 4)) with hsdef
  have hs0 : 0 < s := lt_min hδw (lt_min hδw20 (by norm_num))
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
  have hd : period - sweepW' D σ₀ < ε₁ / (2 * C) := by
    have h := hδw' σ₀ hdist
    rw [Real.dist_eq, hW1] at h
    have hle : sweepW' D σ₀ ≤ period := (sweepW'_nonneg_le D σ₀).2
    have h2 : period - sweepW' D σ₀ = |sweepW' D σ₀ - period| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [h2]; exact h
  have hd0 : 0 < period - sweepW' D σ₀ := sub_pos.mpr (sweepW'_lt_period D hσ₀1)
  have hsum : ε₁ / (2 * C) + ε₁ / (2 * C) = ε₁ / C := by
    rw [eq_div_iff hCne]
    field_simp
    ring
  have hlamd : lay + (period - sweepW' D σ₀) ≤ ε₁ / C := by
    linarith [hlayHalf, hd.le, hsum]
  have hfine : C * (lay + (period - sweepW' D σ₀)) ≤ ε₁ := by
    have h1 := mul_le_mul_of_nonneg_left hlamd hCpos.le
    have h2 : C * (ε₁ / C) = ε₁ := mul_div_cancel₀ ε₁ hCne
    linarith [h1, h2.le, h2.ge]
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]
    nlinarith [hM₂0, hCv0, period_pos]
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
  exact ⟨σ₀, δ₁, δ₂, 0, Θ, hσ₀half, hσ₀1, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hfine, hΘsm, hΘsh,
    hΘpos, fun t => by simpa [hEq] using hΘ1 t, fun t => by simpa [hEq] using hΘ2 t⟩

end Work.Drive
