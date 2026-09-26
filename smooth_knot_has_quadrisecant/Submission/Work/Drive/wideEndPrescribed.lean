import Mathlib
import Submission.Work.Drive.sweepFam_wideEnd_estimate_tol

/-!
# The wide-end estimate at a *prescribed* chamfer fraction

`Work.Drive.sweepFam_wideEnd_estimate_tol` produces its chamfer fraction `lam` *existentially*
(`lam = min(min L (1/4)) ((period − W_σ₀)/period)/2`).  The `OFat` endgame cannot use that form: its
slices clause (`Work.Drive.exists_lam_L_slicesClause_sweepFam_of_ofat`) provides **one** `lam` per
(window, ρ) — the deep cut `lam = ρ/δA` — so the top end must be able to run at a *prescribed* `lam`.

The fine regime of the wide-end estimate is exactly the condition

    `16 (Cv+1) (lam·period + d)^2 ≤ ε₁`   and   `16 (M₂+1) (1+period) (lam + d) ≤ ε₁`,
    `d := period - sweepW' D σ₀`,

and it is achievable for *every* `lam ≤ 1/4` as soon as `lam` is bounded by a multiple of `ε₁`: the
`∃ lam` of the sibling is only a packaging artefact.  This module makes that precise, using the
proved `Work.Drive.widePhaseForm` (whose fine-regime hypotheses are already `∀ lam ≤ 1/4`) and the
phase transfer `Work.Drive.reparamOfPhase`.
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real

/-- **The wide-end estimate at a prescribed fraction.**  There is a constant `C > 0` (a function of
the knot and the sweep data) such that for every tolerance `ε₁ ∈ (0, C]`, every width budget `L > 0`
and every prescribed fraction `lam ∈ (0, min L (1/4)]` with `2 C lam ≤ ε₁`, there are a sweep
parameter `σ₀ ∈ (1/2, 1)`, widths `δ₁, δ₂ ≤ L` and a `C^∞`, `period`-shifting reparametrisation `Θ`
with `deriv Θ > 0` carrying the slice `sweepFam r D lam δ₁ δ₂ σ₀` into the `ε₁`-neighbourhood (both
`C⁰` and `C¹`) of the knot `r`, with `C (lam + (period - sweepW' D σ₀)) ≤ ε₁`. -/
theorem wideEnd_prescribed {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ C → ∀ L : ℝ, 0 < L →
      ∀ lam : ℝ, 0 < lam → lam ≤ L → lam ≤ 1 / 4 → 2 * C * lam ≤ ε₁ →
        ∃ (σ₀ δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
          1 / 2 < σ₀ ∧ σ₀ < 1 ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
          C * (lam + (period - sweepW' D σ₀)) ≤ ε₁ ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
          (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
          (∀ t : ℝ, 0 < deriv Θ t) ∧
          (∀ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
          (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
            - velocity r (t + c)‖ < ε₁) := by
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
  intro ε₁ hε₁0 hε₁C L hL lam hlam0 hlamL hlam4 h2Clam
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hε2C : 0 < ε₁ / (2 * C) := div_pos hε₁0 (by positivity)
  have hlamHalf : lam ≤ ε₁ / (2 * C) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * C)]
    linarith
  -- a sweep parameter near `1` whose gap `period - W` is below `ε₁/(2C)`
  obtain ⟨δw, hδw, hδw'⟩ := Metric.continuous_iff.mp (sweepW'_continuous D) 1 (ε₁ / (2 * C)) hε2C
  set ρw : ℝ := min δw (1 / 4) with hρw
  have hρw0 : 0 < ρw := lt_min hδw (by norm_num)
  have hρw1 : ρw ≤ 1 / 4 := min_le_right _ _
  set σ₀ : ℝ := 1 - ρw / 2 with hσ₀
  have hσ₀gt : 1 / 2 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀lt : σ₀ < 1 := by rw [hσ₀]; linarith
  have hσ₀0 : 0 < σ₀ := by linarith
  have hdist : dist σ₀ 1 < δw := by
    rw [Real.dist_eq, hσ₀]
    have h1 : |1 - ρw / 2 - 1| = ρw / 2 := by
      rw [show (1 - ρw / 2 - 1) = -(ρw / 2) by ring, abs_neg, abs_of_nonneg (by linarith [hρw0])]
    rw [h1]
    have hle : ρw ≤ δw := by rw [hρw]; exact min_le_left _ _
    linarith [hρw0, hle]
  have hW1 : sweepW' D 1 = period := sweepW'_eq_period_of_one_le D le_rfl
  have hd : period - sweepW' D σ₀ < ε₁ / (2 * C) := by
    have h := hδw' σ₀ hdist
    rw [Real.dist_eq, hW1] at h
    have hle : sweepW' D σ₀ ≤ period := (sweepW'_nonneg_le D σ₀).2
    have h2 : period - sweepW' D σ₀ = |sweepW' D σ₀ - period| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [h2]; exact h
  have hd0 : 0 < period - sweepW' D σ₀ := sub_pos.mpr (sweepW'_lt_period D hσ₀lt)
  have hsum : ε₁ / (2 * C) + ε₁ / (2 * C) = ε₁ / C := by
    rw [eq_div_iff hCne]
    field_simp
    ring
  have hlamd : lam + (period - sweepW' D σ₀) ≤ ε₁ / C := by
    linarith [hlamHalf, hd.le, hsum]
  have hfine : C * (lam + (period - sweepW' D σ₀)) ≤ ε₁ := by
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
  have hdC : lam * period + (period - sweepW' D σ₀) ≤ (1 + period) * (ε₁ / C) := by
    have hper1 : (1 : ℝ) ≤ period := by rw [period]; linarith [Real.pi_gt_three]
    nlinarith [hlamd, hper1, hlam0, hd0]
  have hCv1 : (0 : ℝ) ≤ 16 * (Cv + 1) := by linarith
  have hM21 : (0 : ℝ) ≤ 16 * (M₂ + 1) * (1 + period) := by
    have := period_pos; nlinarith [hM₂0]
  have hvalε : 16 * (Cv + 1) * (lam * period + (period - sweepW' D σ₀)) ^ 2 ≤ ε₁ := by
    have hnn : 0 ≤ lam * period + (period - sweepW' D σ₀) := by
      have h := mul_nonneg hlam0.le period_pos.le; linarith [hd0]
    have h2 : (lam * period + (period - sweepW' D σ₀)) ^ 2 ≤ ((1 + period) * (ε₁ / C)) ^ 2 :=
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
  have hvelε : 16 * (M₂ + 1) * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε₁ := by
    have h8 : 16 * (M₂ + 1) * (1 + period) * (lam + (period - sweepW' D σ₀))
        = (16 * (M₂ + 1) * (1 + period)) * (lam + (period - sweepW' D σ₀)) := by ring
    rw [h8]
    calc (16 * (M₂ + 1) * (1 + period)) * (lam + (period - sweepW' D σ₀))
        ≤ (16 * (M₂ + 1) * (1 + period)) * (ε₁ / C) := mul_le_mul_of_nonneg_left hlamd hM21
      _ ≤ C * (ε₁ / C) := mul_le_mul_of_nonneg_right hCa hx0
      _ = ε₁ := mul_div_cancel₀ ε₁ hCne
  -- the phase, and its transfer to the knot
  obtain ⟨δ₁, δ₂, ψ, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hψsm, hψsh, hψpos, hψ1, hψ2⟩ :=
    widePhaseForm hr D hM₁ hM₂0.le hM₂ hCv0.le hσ₀0 hσ₀lt (wideSig_tau_lipschitz D)
      (wideSig_sigma_modulus D σ₀) hval hvel hε₁0 hL hlam0 hlamL hlam4 hvalε hvelε
  obtain ⟨Θ, hΘsm, hΘsh, hΘpos, hΘ1, hΘ2⟩ :=
    reparamOfPhase (r := r) (Φ := fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u)
      hψsm hψsh hψpos hε₁0
      ((sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ (ne_of_gt hδ₁0)
        (ne_of_gt hδ₂0)).2.2 σ₀) hψ1 hψ2
  exact ⟨σ₀, δ₁, δ₂, 0, Θ, hσ₀gt, hσ₀lt, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hfine, hΘsm, hΘsh,
    hΘpos, fun t => by simpa using hΘ1 t, fun t => by simpa using hΘ2 t⟩

end Work.Drive
