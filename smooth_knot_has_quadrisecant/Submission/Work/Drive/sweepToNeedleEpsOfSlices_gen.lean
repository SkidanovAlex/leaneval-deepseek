import Mathlib
import Submission.Work.Drive.sweepToNeedleEpsOfSlices
import Submission.Work.Drive.wideEndPrescribedGen
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.chamferLoopGen_locallyIntegrable
import Submission.Work.Drive.sweepFamOf_contDiff_periodic_li

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## The wide-end estimate with the slice chosen before the layout and the widths

`Work.Drive.wideEndPrescribedGen` chooses the *slice* `σ₀` only after the chamfer fraction `lay` and
the width budget `L` have been fixed.  The endgame below has to pick `σ₀` *first*, because the
slices-clause threshold of `hsl` (and hence the admissible sizes of `lay` and of the two blur
widths) depends on the slice.  This lemma records that the same estimate is available with `σ₀`
moved in front of both quantifiers: the proof of `wideEndPrescribedGen` selects
`σ₀ = 1 - s/2` with `s` a function of `ε₁`, `δs` and `D` alone, and every remaining estimate only
uses `lay` through the *upper* bound `2 * C * lay ≤ ε₁`. -/
theorem wideEndPrescribedGen_sigmaFirst {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {ρ₀ δs cQ : ℝ} (hδs : 0 < δs) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ C →
      ∃ σ₀ : ℝ, 1 / 2 < σ₀ ∧ σ₀ < 1 ∧
        ∀ lay : ℝ, 0 < lay → lay ≤ 1 / 4 → 2 * C * lay ≤ ε₁ →
          C * (lay + (period - sweepW' D σ₀)) ≤ ε₁ ∧
          ∀ L : ℝ, 0 < L →
            ∃ (δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
              0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
              ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
              (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
              (∀ t : ℝ, 0 < deriv Θ t) ∧
              (∀ t : ℝ, ‖sweepFamOf (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                  (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
              (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFamOf (chamferLoopGen r D lay
                  (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ u)) t
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
  intro ε₁ hε₁0 hε₁C
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hε2C : 0 < ε₁ / (2 * C) := div_pos hε₁0 (by positivity)
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
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]
    nlinarith [hM₂0, hCv0, period_pos]
  -- the two fine-regime conditions
  have hxC : ε₁ / C ≤ 1 := by
    rw [div_le_one hCpos]
    exact hε₁C
  have hx0 : 0 ≤ ε₁ / C := div_nonneg hε₁0.le hCpos.le
  have hx2 : (ε₁ / C) ^ 2 ≤ ε₁ / C := by nlinarith [hx0, hxC]
  have hCv1 : (0 : ℝ) ≤ 16 * (Cv + 1) := by linarith
  have hM21 : (0 : ℝ) ≤ 16 * (M₂ + 1) * (1 + period) := by
    have := period_pos; nlinarith [hM₂0]
  refine ⟨σ₀, hσ₀half, hσ₀1, ?_⟩
  intro lay hlay0 hlay4 h2Clam
  have hlayHalf : lay ≤ ε₁ / (2 * C) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
    nlinarith [h2Clam]
  have hlamd : lay + (period - sweepW' D σ₀) ≤ ε₁ / C := by
    linarith [hlayHalf, hd.le, hsum]
  have hfine : C * (lay + (period - sweepW' D σ₀)) ≤ ε₁ := by
    have h1 := mul_le_mul_of_nonneg_left hlamd hCpos.le
    have h2 : C * (ε₁ / C) = ε₁ := mul_div_cancel₀ ε₁ hCne
    linarith [h1, h2.le, h2.ge]
  have hdC : lay * period + (period - sweepW' D σ₀) ≤ (1 + period) * (ε₁ / C) := by
    have hper1 : (1 : ℝ) ≤ period := by rw [period]; linarith [Real.pi_gt_three]
    nlinarith [hlamd, hper1, hlay0, hd0]
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
  refine ⟨hfine, ?_⟩
  intro L hL
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

open LeanEval.KnotTheory.Quadrisecant in
/-- The top end of the uniform-`ρ₀` endgame, for the scheduled chamfer loop: the transcription of
`Work.Drive.sweepToNeedleEpsOfSlices` with the scheduled loop `chamferLoopGen r D lay (schedAlpha …)
(schedBeta …)` in place of `sweepLoopChamfer r D lay`, the blurred family `sweepFamOf` in place of
`sweepFam`, and the endpoint at the blurred scheduled slice `σ = ε`. -/
theorem sweepToNeedleEpsOfSlices_gen {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {ρ₀ δs cQ : ℝ} (hδs : 0 < δs)
    (hsl : ∀ ε σ₀ : ℝ, 0 < ε → ε < σ₀ → σ₀ < 1 →
      ∃ L : ℝ, 0 < L ∧
        ∀ (lay δ₁ δ₂ : ℝ), 0 < lay → lay ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
          ∀ σ : ℝ, ε ≤ σ → σ ≤ σ₀ →
            Set.InjOn (fun t : ℝ => sweepFamOf
                (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
                δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
            (∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf
                (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
                δ₁ δ₂ σ t) t ≠ 0))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ Δ : ℝ, 0 < Δ →
      ∃ (lay δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
        (0 < lay ∧ lay < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
          lay ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
        IsSmoothKnot r0 ∧
        (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
        ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ s t : ℝ, H (t + period) s = H t s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => H t s)) ∧
        (∀ t : ℝ, H t 0 = r0 t) ∧
        (∀ t : ℝ, H t 1 = sweepFamOf
            (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
            δ₁ δ₂ ε t) := by
  intro Δ hΔ
  -- ## (a) the uniform small-correction threshold of the knot
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hle0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hrotjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => r (p.1 + p.2 * period)) := by
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + p.2 * period) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hrotper : ∀ s t : ℝ, r ((t + period) + s * period) = r (t + s * period) := by
    intro s t
    have h : t + period + s * period = (t + s * period) + period := by ring
    rw [h, hr.periodic]
  have hrotsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => r (t + s * period)) := by
    intro s hs
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (s * period)
  obtain ⟨ε_uc, hε_uc_pos, h_uc⟩ := uniformCorrection_clauses hrotjoint hrotper hrotsl
  -- ## (b) the wide end, with the slice `σ₀` chosen *before* the layout and the widths
  obtain ⟨C, hCpos, hCsw⟩ :=
    wideEndPrescribedGen_sigmaFirst (r := r) hr D (ρ₀ := ρ₀) (δs := δs) (cQ := cQ) hδs
  set ε₁ : ℝ := min ε_uc (C / 2) with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε_uc_pos (by linarith)
  have hε₁uc : ε₁ ≤ ε_uc := min_le_left _ _
  have hε₁C : ε₁ ≤ C := le_trans (min_le_right _ _) (by linarith)
  obtain ⟨σ₀, hσ₀half, hσ₀lt, hσ₀sw⟩ := hCsw ε₁ hε₁pos hε₁C
  have hεσ₀ : ε < σ₀ := lt_trans hε1 hσ₀half
  -- ## (c) the slices clause at `σ₀` fixes the layout; then the widths
  obtain ⟨Ls, hLs0, hLs⟩ := hsl ε σ₀ hε hεσ₀ hσ₀lt
  set lay : ℝ := min (min Δ (1 / 4)) (min (ε₁ / (2 * C)) Ls) with hlaydef
  have h2Cpos : (0 : ℝ) < 2 * C := by linarith
  have hlay0 : 0 < lay := by
    rw [hlaydef]
    exact lt_min (lt_min hΔ (by norm_num)) (lt_min (by positivity) hLs0)
  have hlay4 : lay ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hlayΔ : lay ≤ Δ := (min_le_left _ _).trans (min_le_left _ _)
  have hlayLs : lay ≤ Ls := (min_le_right _ _).trans (min_le_right _ _)
  have hlayeps : lay ≤ ε₁ / (2 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have h2Clam : 2 * C * lay ≤ ε₁ := by
    have h := mul_le_mul_of_nonneg_left hlayeps h2Cpos.le
    have he : 2 * C * (ε₁ / (2 * C)) = ε₁ := by field_simp
    linarith [h, he.le, he.ge]
  obtain ⟨hfine, hsw⟩ := hσ₀sw lay hlay0 hlay4 h2Clam
  set Lw : ℝ := min Ls (min Δ (min (ε / 4) (1 / 4))) with hLwdef
  have hLw0 : 0 < Lw := by
    rw [hLwdef]
    exact lt_min hLs0 (lt_min hΔ (lt_min (by linarith) (by norm_num)))
  obtain ⟨δ₁, δ₂, c, Θ, hδ₁0, hδ₁Lw, hδ₂0, hδ₂Lw, hΘsm, hΘsh, hΘpos, hcl1, hcl2⟩ :=
    hsw Lw hLw0
  have hδ₁Ls : δ₁ ≤ Ls := hδ₁Lw.trans (min_le_left _ _)
  have hδ₂Ls : δ₂ ≤ Ls := hδ₂Lw.trans (min_le_left _ _)
  have hδ₁Δ : δ₁ ≤ Δ := hδ₁Lw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂Δ : δ₂ ≤ Δ := hδ₂Lw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂ε : δ₂ ≤ ε / 2 := by
    have h : δ₂ ≤ ε / 4 :=
      hδ₂Lw.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hδ₁ne : δ₁ ≠ 0 := ne_of_gt hδ₁0
  have hδ₂ne : δ₂ ≠ 0 := ne_of_gt hδ₂0
  -- ## (d) the scheduled loop and the structural clauses of its blurred family
  let Γ : ℝ → ℝ → Space :=
    chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D)
  have hLI : MeasureTheory.LocallyIntegrable (fun p : ℝ × ℝ => Γ p.1 p.2) MeasureTheory.volume :=
    chamferLoopGen_locallyIntegrable (r := r) hr (D := D) (lay := lay) (ρ₀ := ρ₀) (δs := δs)
      (cQ := cQ) hlay0 hδs
  have hperΓ : ∀ s t : ℝ, Γ s (t + period) = Γ s t :=
    fun s t => chamferLoopGen_periodic_t D lay (schedAlpha lay ρ₀ δs D)
      (schedBeta r lay ρ₀ δs cQ D) s t
  obtain ⟨hsmjoint, hsmper, hsmslice⟩ :=
    sweepFamOf_contDiff_periodic_li Γ hLI hperΓ δ₁ δ₂ hδ₁ne hδ₂ne
  have hσcl : ∀ σ ∈ Set.Icc ε σ₀,
      Set.InjOn (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
      (∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) t ≠ 0) :=
    fun σ hσ => hLs lay δ₁ δ₂ hlay0 hlayLs hδ₁0 hδ₁Ls hδ₂0 hδ₂Ls σ hσ.1 hσ.2
  -- ## (e) the shifted knot `K`, the wide-end slice `G`, and the correction `w`
  let K : ℝ → Space := fun t => r (t + c)
  let G : ℝ → Space := fun t => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t)
  let w : ℝ → Space := fun t => G t - K t
  have hKsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => r (t + c))
    exact (hr.smooth.of_le le_top).comp (by
      simpa using (contDiff_id.add contDiff_const :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t + c)))
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t))
    exact (hsmslice σ₀).comp hΘsm
  have hwsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G - K)
    exact hGsmooth.sub hKsmooth
  have hwper : Function.Periodic w period := by
    intro t
    change G (t + period) - K (t + period) = G t - K t
    have h1 : G (t + period) = G t := by
      change sweepFamOf Γ δ₁ δ₂ σ₀ (Θ (t + period)) = sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t)
      rw [hΘsh t, hsmper]
    have h2 : K (t + period) = K t := by
      change r (t + period + c) = r (t + c)
      rw [show t + period + c = (t + c) + period from by ring]
      exact hr.periodic (t + c)
    rw [h1, h2]
  have hwbd : ∀ t : ℝ, ‖w t‖ < ε_uc := by
    intro t
    have h : ‖w t‖ < ε₁ := by
      change ‖sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁
      exact hcl1 t
    exact lt_of_lt_of_le h hε₁uc
  have hwvel : ∀ t : ℝ, ‖velocity w t‖ < ε_uc := by
    intro t
    have h := hcl2 t
    have hderiv : velocity w t
        = deriv (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c) := by
      change deriv (fun u : ℝ => G u - K u) t
        = deriv (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c)
      rw [show (fun u : ℝ => G u - K u)
          = (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) - fun u : ℝ => r (u + c) from rfl]
      rw [deriv_sub]
      · congr 1
        change deriv (fun u : ℝ => r (u + c)) t = deriv r (t + c)
        exact deriv_shift r ((hr.smooth.of_le le_top).differentiable hle0 (t + c))
      · exact (hGsmooth.differentiable hle0) t
      · exact DifferentiableAt.comp t
          ((hr.smooth.of_le le_top).differentiable hle0 (t + c)) (by fun_prop)
    rw [hderiv]
    exact lt_of_lt_of_le h hε₁uc
  -- ## (f) phase A: rotations of the knot
  let A : ℝ → ℝ → Space := fun t p => r (t + c * p)
  have hAjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => r (p.1 + c * p.2))
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + c * p.2) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hAper : ∀ s t : ℝ, A (t + period) s = A t s := by
    intro s t
    change r (t + period + c * s) = r (t + c * s)
    rw [show t + period + c * s = (t + c * s) + period from by ring]
    exact hr.periodic _
  have hAslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => A t s) := by
    intro s hs
    change IsCInfKnot (fun t : ℝ => r (t + c * s))
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (c * s)
  have hA1 : ∀ t : ℝ, A t 1 = K t := by
    intro t
    change r (t + c * 1) = r (t + c)
    ring_nf
  have hA0 : ∀ t : ℝ, A t 0 = r t := by
    intro t
    change r (t + c * 0) = r t
    simp
  -- ## (g) phase B: from the shifted knot to the wide-end slice
  let B : ℝ → ℝ → Space := fun t p => K t + p • w t
  have hBjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => K p.1 + p.2 • w p.1)
    refine (hKsmooth.of_le hle).comp contDiff_fst |>.add ?_
    exact contDiff_snd.smul ((hwsmooth.of_le hle).comp contDiff_fst)
  have hBper : ∀ s t : ℝ, B (t + period) s = B t s := by
    intro s t
    change K (t + period) + s • w (t + period) = K t + s • w t
    rw [show K (t + period) = K t from by
      change r (t + period + c) = r (t + c)
      rw [show t + period + c = (t + c) + period from by ring]
      exact hr.periodic (t + c), hwper t]
  have hB0 : ∀ t : ℝ, B t 0 = K t := by
    intro t
    change K t + (0 : ℝ) • w t = K t
    simp
  have hB1 : ∀ t : ℝ, B t 1 = G t := by
    intro t
    change K t + (1 : ℝ) • (G t - K t) = G t
    rw [one_smul]
    abel
  have hBslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => B t s) := by
    intro s hs
    have hnorm1 : ∀ t : ℝ, ‖s • w t‖ < ε_uc := by
      intro t
      rw [norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖w t‖ ≤ 1 * ‖w t‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖w t‖ := one_mul _
        _ < ε_uc := hwbd t
    have hnorm2 : ∀ t : ℝ, ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc := by
      intro t
      have hd : deriv (fun u : ℝ => s • w u) t = s • velocity w t := by
        show deriv (fun u : ℝ => s • w u) t = s • deriv w t
        exact (((hwsmooth.differentiable hle0) t).hasDerivAt.const_smul s).deriv
      rw [hd, norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖velocity w t‖ ≤ 1 * ‖velocity w t‖ :=
            mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖velocity w t‖ := one_mul _
        _ < ε_uc := hwvel t
    have hWsm : ContDiff ℝ 1 (fun q : ℝ × ℝ => s • w q.1) :=
      ((hwsmooth.of_le hle).comp contDiff_fst).const_smul s
    have hWper : ∀ a t : ℝ, s • w (t + period) = s • w t := by
      intro a t; rw [hwper t]
    have hWsmall : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖s • w t‖ < ε_uc ∧ ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc :=
      fun a ha t => ⟨hnorm1 t, hnorm2 t⟩
    obtain ⟨hc1, hc2, hc3⟩ := h_uc (fun t a => s • w t) hWsm hWper hWsmall
      (sweepParam c) ⟨(sweepParam_mem c).1, (sweepParam_mem c).2.le⟩
    have hshift : (fun t : ℝ => r (t + sweepParam c * period) + s • w t)
        = fun t : ℝ => B t s := by
      funext t
      change r (t + sweepParam c * period) + s • w t = r (t + c) + s • w t
      congr 1
      exact (shift_eq_mod hr.periodic c t).symm
    rw [hshift] at hc1 hc2 hc3
    refine ⟨?_, hc1, hc2, hc3⟩
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => r (t + c) + s • w t)
    exact hKsmooth.add (hwsmooth.const_smul s)
  -- ## (h) phase C: the sweep itself, reparametrised
  have hΘ1 : ContDiff ℝ 1 Θ := hΘsm.of_le hle
  obtain ⟨hθjoint1, hθderiv, hθshift⟩ := interpTheta_facts hΘ1 hΘsh hΘpos
  have hθsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 - q.2) * Θ q.1 + q.2 * q.1) := interpTheta_smooth hΘsm
  let σfun : ℝ → ℝ := fun p => ε + (σ₀ - ε) * (1 - gluePsi p)
  let θfun : ℝ → ℝ → ℝ := fun p t => (1 - p) * Θ t + p * t
  let Cc : ℝ → ℝ → Space := fun t p => sweepFamOf Γ δ₁ δ₂ (σfun p) (θfun p t)
  have hσmem : ∀ p ∈ Set.Icc (0 : ℝ) 1, ε ≤ σfun p ∧ σfun p ≤ σ₀ := by
    intro p hp
    have hg : gluePsi p ∈ Set.Icc (0 : ℝ) 1 := gluePsi_facts.2.2.1 p hp
    have hsub : 0 ≤ σ₀ - ε := by linarith
    change ε ≤ ε + (σ₀ - ε) * (1 - gluePsi p) ∧ ε + (σ₀ - ε) * (1 - gluePsi p) ≤ σ₀
    have h1 : 0 ≤ (σ₀ - ε) * (1 - gluePsi p) := mul_nonneg hsub (by linarith [hg.2])
    have h2 : (σ₀ - ε) * (1 - gluePsi p) ≤ σ₀ - ε := by
      have h3 : (1 - gluePsi p) ≤ 1 := by linarith [hg.1]
      nlinarith [hsub, h3]
    exact ⟨by linarith, by linarith⟩
  have hσc1 : ContDiff ℝ 1 σfun := by
    change ContDiff ℝ 1 (fun p : ℝ => ε + (σ₀ - ε) * (1 - gluePsi p))
    have hg : ContDiff ℝ 1 gluePsi := gluePsi_facts.2.2.2.2
    exact contDiff_const.add (contDiff_const.mul (contDiff_const.sub hg))
  have hCcjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => Cc p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => sweepFamOf Γ δ₁ δ₂ (σfun p.2) (θfun p.2 p.1))
    have hinner : ContDiff ℝ 1 (fun q : ℝ × ℝ => (σfun q.2, θfun q.2 q.1)) := by
      refine (hσc1.comp contDiff_snd).prodMk ?_
      change ContDiff ℝ 1 (fun q : ℝ × ℝ => (1 - q.2) * Θ q.1 + q.2 * q.1)
      exact hθjoint1
    have hcomp := hsmjoint.comp hinner
    simpa only [Function.comp_def] using hcomp
  have hCcper : ∀ s t : ℝ, Cc (t + period) s = Cc t s := by
    intro s t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s))
        ((1 - s) * Θ (t + period) + s * (t + period))
      = sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s)) ((1 - s) * Θ t + s * t)
    rw [show (1 - s) * Θ (t + period) + s * (t + period)
        = ((1 - s) * Θ t + s * t) + period from by rw [hΘsh t]; ring]
    exact hsmper _ _
  have hCcslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => Cc t s) := by
    intro s hs
    have hmem := hσmem s hs
    have hslic : IsCInfKnot (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ (σfun s) t) :=
      ⟨hsmslice (σfun s), hsmper (σfun s), (hσcl (σfun s) hmem).1, (hσcl (σfun s) hmem).2⟩
    have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => θfun s t) := by
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (1 - s) * Θ t + s * t)
      exact hθsmooth.comp (contDiff_id.prodMk contDiff_const)
    have hgshift : ∀ t : ℝ, θfun s (t + period) = θfun s t + period := by
      intro t
      change (1 - s) * Θ (t + period) + s * (t + period) = (1 - s) * Θ t + s * t + period
      rw [hΘsh t]; ring
    have hgderiv : ∀ t : ℝ, 0 < deriv (fun u : ℝ => θfun s u) t := by
      intro t
      have h := hθderiv s hs t
      rwa [show (fun u : ℝ => θfun s u) = fun u : ℝ => (1 - s) * Θ u + s * u from
        funext fun u => rfl] at h
    have hcomp := isCInfKnot_comp_reparam hgsmooth hgshift hgderiv hslic
    change IsCInfKnot (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ (σfun s) (θfun s t))
    simpa only [Function.comp_def] using hcomp
  have hCc0 : ∀ t : ℝ, Cc t 0 = G t := by
    intro t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 0)) ((1 - 0) * Θ t + 0 * t) = G t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 0) = σ₀ := by rw [gluePsi_facts.1]; ring
    have h2 : (1 - 0) * Θ t + 0 * t = Θ t := by ring
    rw [h1, h2]
  have hCc1 : ∀ t : ℝ, Cc t 1 = sweepFamOf Γ δ₁ δ₂ ε t := by
    intro t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 1)) ((1 - 1) * Θ t + 1 * t)
      = sweepFamOf Γ δ₁ δ₂ ε t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 1) = ε := by rw [gluePsi_facts.2.1]; ring
    have h2 : (1 - 1) * Θ t + 1 * t = t := by ring
    rw [h1, h2]
  -- ## (i) gluing the three phases
  let AB : ℝ → ℝ → Space := fun t s => sweepGlue A B s t
  obtain ⟨hABjoint, hABper, hABslice, hAB0, hAB1⟩ :=
    sweepGlue_clauses hAjoint hBjoint (fun t => (hA1 t).trans (hB0 t).symm)
      hAslice hBslice hAper hBper
  have hAB0' : ∀ t : ℝ, AB t 0 = A t 0 := hAB0
  have hjun : ∀ t : ℝ, AB t 1 = Cc t 0 := by
    intro t
    change sweepGlue A B 1 t = Cc t 0
    rw [hAB1 t, hB1 t, hCc0 t]
  obtain ⟨hHjoint, hHper, hHslice, hH0, hH1⟩ :=
    sweepGlue_clauses hABjoint hCcjoint hjun hABslice hCcslice hABper hCcper
  refine ⟨lay, δ₁, δ₂, r, fun t s => sweepGlue AB Cc s t,
    ⟨hlay0, by linarith, hδ₁0, hδ₂0, hδ₂ε, hlayΔ, hδ₁Δ, hδ₂Δ⟩, hr, ?_, hHjoint, hHper,
    hHslice, ?_, ?_⟩
  · intro t
    exact ⟨by rw [sub_self, norm_zero]; exact hδ, by rw [sub_self, norm_zero]; exact hδ⟩
  · intro t
    change sweepGlue AB Cc 0 t = r t
    rw [hH0, hAB0']
    exact hA0 t
  · intro t
    change sweepGlue AB Cc 1 t = sweepFamOf Γ δ₁ δ₂ ε t
    rw [hH1]
    exact hCc1 t


end Work.Drive
