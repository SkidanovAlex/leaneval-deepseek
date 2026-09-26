import Mathlib
import Submission.Work.Drive.wideEndPrescribedGen

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real

/- **The wide-end estimate at a *prescribed* sweep parameter, for the scheduled loop.**

This is `Work.Drive.wideEndPrescribedGen` with the quantifier order repaired: instead of producing
the trough slice `σ₀` after the tolerance `ε₁` and the width budget `L` (an order that makes the
wrapper circular), the slice is an *input*, together with the size hypothesis
`C * (lay + (period - W_σ₀)) ≤ ε₁` which is exactly the condition the estimate needs.  The modulus
of continuity of `σ ↦ W_σ` at `1` is independent of `ε₁`, so the trough neighbourhood radius `ν` can
be fixed once and for all. -/
open LeanEval.KnotTheory.Quadrisecant Set in
theorem wideEndGivenC {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lay ρ₀ δs cQ : ℝ} (hlay0 : 0 < lay) (hlay4 : lay ≤ 1 / 4) (hδs : 0 < δs) :
    ∃ Cmin ν : ℝ, 0 < Cmin ∧ 0 < ν ∧ ν ≤ 1 / 2 ∧
      (∀ C : ℝ, Cmin ≤ C →
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ C → 2 * C * lay ≤ ε₁ → ∀ L : ℝ, 0 < L → ∀ σ₀ : ℝ,
        dist σ₀ 1 < ν → σ₀ < 1 →
        C * (lay + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ≤ ε₁ →
        ∃ (δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
          0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
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
            - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁) ) := by
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
  -- the `ε₁`-independent trough radius of the schedule: the modulus of continuity of `W` at `1`
  have htol2 : 0 < min (period / 2) (δs / 8) :=
    lt_min (half_pos period_pos) (by linarith [hδs])
  obtain ⟨δw2, hδw20, hδw2'⟩ :=
    Metric.continuous_iff.mp (sweepW'_continuous D) 1 (min (period / 2) (δs / 8)) htol2
  set ν : ℝ := min (δw2 / 2) (1 / 4) with hνdef
  have hν0 : 0 < ν := lt_min (by linarith) (by norm_num)
  have hνle : ν ≤ 1 / 2 := by
    rw [hνdef]
    exact le_trans (min_le_right _ _) (by norm_num)
  have hνd : ν ≤ δw2 / 2 := by rw [hνdef]; exact min_le_left _ _
  have hν4 : ν ≤ 1 / 4 := by rw [hνdef]; exact min_le_right _ _
  refine ⟨Cmin, ν, hCminpos, hν0, hνle, ?_⟩
  intro C hCge ε₁ hε₁0 hε₁C h2Clam L hL σ₀ hσdist hσ₀lt1 hwide
  have hCpos : 0 < C := lt_of_lt_of_le hCminpos hCge
  have hCa : 16 * (M₂ + 1) * (1 + period) ≤ C := le_trans hCmina hCge
  have hCb : 16 * (Cv + 1) * (1 + period) ^ 2 ≤ C := le_trans hCminb hCge
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hW1 : sweepW' D 1 = period := sweepW'_eq_period_of_one_le D le_rfl
  -- the prescribed slice lies in `(3/4, 1)`
  have hdist1 : |σ₀ - 1| < ν := by
    rw [Real.dist_eq] at hσdist
    exact hσdist
  have hσ₀half : 1 / 2 < σ₀ := by
    have h := (abs_lt.mp hdist1).1
    linarith [hν4]
  have hσ₀0 : 0 < σ₀ := by linarith
  have hσ₀1 : σ₀ < 1 := hσ₀lt1
  -- the size hypothesis in the form the budget consumes
  have hlamd : lay + (period - sweepW' D σ₀) ≤ ε₁ / C := by
    rw [le_div_iff₀ hCpos]
    calc (lay + (period - sweepW' D σ₀)) * C
        = C * (lay + (period - sweepW' D σ₀)) := by ring
      _ ≤ ε₁ := hwide
  have hd0 : 0 < period - sweepW' D σ₀ := sub_pos.mpr (sweepW'_lt_period D hσ₀1)
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
  -- the width budget: `min L (δw2/8)`, so that the widths keep the blur window inside the trough
  set Lw : ℝ := min L (δw2 / 8) with hLwdef
  have hLw0 : 0 < Lw := lt_min hL (by linarith)
  have hLwL : Lw ≤ L := min_le_left _ _
  have hLw8 : Lw ≤ δw2 / 8 := min_le_right _ _
  obtain ⟨δ₁, δ₂, ψ, hδ₁0, hδ₁Lw, hδ₂0, hδ₂Lw, hψsm, hψsh, hψpos, hψ1, hψ2⟩ :=
    widePhaseFormBudget hr D hM₁ hM₂0.le hM₂ hCv0.le hσ₀0 hσ₀1 (wideSig_tau_lipschitz D)
      (wideSig_sigma_modulus D σ₀) hval hvel hε₁0 hLw0 hlay0 hlay4 hvalε hvelε
  have hδ₁L : δ₁ ≤ L := le_trans hδ₁Lw hLwL
  have hδ₂L : δ₂ ≤ L := le_trans hδ₂Lw hLwL
  have hδ₂8 : δ₂ ≤ δw2 / 8 := le_trans hδ₂Lw hLw8
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
      have hC2 : |δ₂ * v| ≤ δ₂ := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hδ₂0)]
        nlinarith [hvabs, hδ₂0.le]
      calc dist (σ₀ - δ₂ * v) 1 ≤ dist (σ₀ - δ₂ * v) σ₀ + dist σ₀ 1 := dist_triangle _ _ _
        _ = |δ₂ * v| + dist σ₀ 1 := by rw [hA]
        _ ≤ δ₂ + ν := by linarith [hσdist]
        _ ≤ δw2 / 8 + δw2 / 2 := by linarith [hδ₂8, hνd]
        _ < δw2 := by linarith [hδw20]
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
