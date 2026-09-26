import Mathlib
import Submission.Work.Drive.widePhaseForm

/-!
# The wide-end phase form with an arbitrary width budget

`Work.Drive.widePhaseForm` (`Submission/Work/Drive/widePhaseForm.lean`) states the wide-end
reparametrisation estimate for the doubly smoothed chord sweep.  Its hypothesis
`hlamL : lam ≤ L` is *not used* by its proof: the width budget `L` only enters as an upper bound for
the two smoothing widths `δ₁, δ₂`, and the estimates do not degrade as the widths shrink.  This
module records the resulting strengthening, which is what the wide-end estimate at a *prescribed*
chamfer fraction needs when the width budget is independent of (and possibly smaller than) that
fraction.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section
set_option maxHeartbeats 4000000

theorem widePhaseFormBudget {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {M₁ M₂ Cv : ℝ} (hM₁ : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ M₁)
    (hM₂0 : 0 ≤ M₂)
    (hM₂ : ∀ x y : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r x
        - LeanEval.KnotTheory.Quadrisecant.velocity r y‖ ≤ M₂ * |x - y|)
    (hCv0 : 0 ≤ Cv)
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hτlip : ∀ (lam' σ τ₁ τ₂ : ℝ), 0 < lam' → lam' ≤ 1 / 4 →
        |Work.Drive.wideSig D lam' σ τ₁ - Work.Drive.wideSig D lam' σ τ₂| ≤ 2 * |τ₁ - τ₂|)
    (hσmod : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 →
        |σ - σ₀| ≤ δ → ‖Work.Drive.wideSig D lam' σ τ - Work.Drive.wideSig D lam' σ₀ τ‖ ≤ η)
    (hval : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ ≤ 1 →
        ‖Work.Drive.sweepLoopChamfer r D lam' σ τ - r (Work.Drive.wideSig D lam' σ τ)‖
          ≤ Cv * (lam' * LeanEval.KnotTheory.Quadrisecant.period
              + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) ^ 2)
    (hvel : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ < 1 →
        ‖Work.Drive.chamferVel r D lam' σ τ -
          Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam'
            (Work.Drive.sweepParam τ) •
          LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.wideSig D lam' σ τ)‖
          ≤ M₂ * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
              (lam' + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) *
            Work.Drive.wideRho (Work.Drive.sweepW' D σ)
              (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam'
              (Work.Drive.sweepParam τ))
    {ε lam L : ℝ} (hε : 0 < ε) (hL : 0 < L) (hlam0 : 0 < lam)
    (hlam4 : lam ≤ 1 / 4)
    (hvalε : 16 * (Cv + 1) * (lam * LeanEval.KnotTheory.Quadrisecant.period
        + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ^ 2 ≤ ε)
    (hvelε : 16 * (M₂ + 1) * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
        (lam + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ₀)) ≤ ε) :
    ∃ (δ₁ δ₂ : ℝ) (ψ : ℝ → ℝ),
      0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t : ℝ, ψ (t + LeanEval.KnotTheory.Quadrisecant.period)
        = ψ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
      (∀ t : ℝ, 0 < deriv ψ t) ∧
      (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ t - r (ψ t)‖ ≤ ε / 2) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ u) t
        - deriv ψ t • LeanEval.KnotTheory.Quadrisecant.velocity r (ψ t)‖
          ≤ (ε / 2) * deriv ψ t) := by
  have hP : 0 < period := period_pos
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hlipr : ∀ x y : ℝ, ‖r x - r y‖ ≤ M₁ * |x - y| := by
    intro x y
    rcases le_total x y with hxy | hxy
    · have hcont : ContDiffOn ℝ 1 r (Set.Icc x y) := (hr.smooth.of_le (by simp)).contDiffOn
      have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := r) hcont hxy
      have h1 : r x - r y = -(∫ z in x..y, velocity r z) := by
        rw [show (∫ z in x..y, velocity r z) = r y - r x from hftc]
        rw [neg_sub]
      rw [h1, norm_neg, abs_sub_comm]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (C := M₁) (fun z _ => hM₁ z)
    · have hcont : ContDiffOn ℝ 1 r (Set.Icc y x) := (hr.smooth.of_le (by simp)).contDiffOn
      have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := r) hcont hxy
      have h1 : r x - r y = ∫ z in y..x, velocity r z := by
        rw [show (∫ z in y..x, velocity r z) = r x - r y from hftc]
      rw [h1]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (C := M₁) (fun z _ => hM₁ z)
  set A : ℝ := M₁ + 2 with hAdef
  set B : ℝ := M₂ + 2 with hBdef
  have hA1 : (1:ℝ) ≤ A := by rw [hAdef]; linarith
  have hB1 : (1:ℝ) ≤ B := by rw [hBdef]; linarith
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hM₁A : M₁ ≤ A := by rw [hAdef]; linarith
  have hM₂B : M₂ ≤ B := by rw [hBdef]; linarith
  set η : ℝ := min 1 (min (ε / (1024 * A)) (ε / (1024 * B))) with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hηA : η ≤ ε / (1024 * A) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηB : η ≤ ε / (1024 * B) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δσ, hδσ0, hδσ⟩ := hσmod η hη0
  obtain ⟨δw, hδw0, hδw⟩ := Metric.continuousAt_iff.mp
    ((sweepLoopChamfer_sweepW'_continuous D).continuousAt)
    (3 * ε / (32 * (M₂ * (1 + period) + 1))) (by positivity)
  obtain ⟨δc, hδc0, hδc⟩ := wf_sweepFam_close_loop hr D hlam0 hlam4 (ε / 8) (by positivity)
  set θ : ℝ := min L (min δc (min δσ (min (δw / 2) (min (σ₀ / 2) (min ((1 - σ₀) / 2)
    (min (ε / (1024 * A)) (min (ε / (1024 * B)) 1))))))) with hθdef
  have hθ0 : 0 < θ := by
    rw [hθdef]
    refine lt_min hL (lt_min hδc0 (lt_min hδσ0 (lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) one_pos)))))))
  have hθL : θ ≤ L := by rw [hθdef]; exact min_le_left _ _
  have hθc : θ ≤ δc := by
    rw [hθdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hθσ : θ ≤ δσ := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθw : θ ≤ δw / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hθs0 : θ ≤ σ₀ / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hθs1 : θ ≤ (1 - σ₀) / 2 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hθA : θ ≤ ε / (1024 * A) := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))))
  have hθB : θ ≤ ε / (1024 * B) := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))))
  have hθσlo : 0 < σ₀ - θ := by linarith
  have hθσhi : σ₀ + θ < 1 := by linarith
  obtain ⟨Vb, hVb0, hVb⟩ := wideEnd_speed_bound hr
  obtain ⟨Rb, hRb0, hRb⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  obtain ⟨AAb, hAAb0, hAAb⟩ := wf_lift_bound D
  have hTwb0 : 0 ≤ 2 * AAb := by positivity
  have hWb : ∀ s : ℝ, |sweepW' D s| ≤ 2 * AAb := by
    intro s
    have h1 := hAAb s
    have h4 : |tbR D s - taR D s| ≤ |tbR D s| + |taR D s| := by
      simpa using abs_sub_le (tbR D s) 0 (taR D s)
    simp only [sweepW']
    linarith [h1.1, h1.2, h4]
  obtain ⟨Cρ, hCρ0, hCρb⟩ := wf_wideRhoFun_bound D hlam0 hlam4
  have hσv : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 → 0 < σ₀ - θ * v ∧ σ₀ - θ * v < 1 := by
    intro v hv
    constructor <;> nlinarith [hv.1, hv.2, hθ0, hθσlo, hθσhi]
  have hηθ : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ w : ℝ,
      |wideSig D lam (σ₀ - θ * v) w - wideSig D lam σ₀ w| ≤ η := by
    intro v hv w
    have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hv.1], hv.2⟩
    have h : |σ₀ - θ * v - σ₀| ≤ δσ := by
      rw [show σ₀ - θ * v - σ₀ = -(θ * v) by ring, abs_neg, abs_mul, abs_of_nonneg hθ0.le]
      calc θ * |v| ≤ θ * 1 := mul_le_mul_of_nonneg_left hv1 hθ0.le
        _ = θ := mul_one _
        _ ≤ δσ := hθσ
    have h' := hδσ lam (σ₀ - θ * v) w hlam0 hlam4 h
    rwa [Real.norm_eq_abs] at h'
  have hψval : ∀ s : ℝ, |widePhaseApprox D lam θ θ σ₀ s - wideSig D lam σ₀ s|
      ≤ 2 * (η + 2 * θ) := fun s =>
    wf_phaseApprox_value D hlam0 hlam4 hθ0.le hηθ (fun a b => hτlip lam σ₀ a b hlam0 hlam4) s
  have hη4 : M₁ * (2 * (η + 2 * θ)) ≤ ε / 16 := by
    have h8 : η + 2 * θ ≤ 3 * (ε / (1024 * A)) := by linarith [hηA, hθA]
    have h10 : M₁ * (2 * (η + 2 * θ)) ≤ A * (2 * (η + 2 * θ)) :=
      mul_le_mul_of_nonneg_right hM₁A (by positivity)
    have h13 : A * (2 * (η + 2 * θ)) ≤ A * (2 * (3 * (ε / (1024 * A)))) :=
      mul_le_mul_of_nonneg_left (by linarith [h8]) (by positivity)
    have h11 : A * (2 * (3 * (ε / (1024 * A)))) ≤ ε / 16 := by
      have h12 : A * (2 * (3 * (ε / (1024 * A)))) = 6 * ε / 1024 := by
        field_simp <;> ring
      rw [h12]; linarith
    exact le_trans h10 (le_trans h13 h11)
  have hvalb : Cv * (lam * period + (period - sweepW' D σ₀)) ^ 2 ≤ ε / 16 := by
    nlinarith [hvalε, hCv0]
  have hσ₀win : 0 < sweepW' D σ₀ ∧ sweepW' D σ₀ < period := by
    have h := sweepW_pos_lt D ⟨σ₀, hσ₀.le, hσ₀1.le⟩ ⟨hσ₀, hσ₀1⟩
    rwa [wf_sweepW'_eq D hσ₀.le hσ₀1.le]
  have hMp : 0 ≤ M₂ * (1 + period) := by positivity
  have hX0 : 0 ≤ lam + (period - sweepW' D σ₀) := by linarith [hlam0, hσ₀win.2]
  have hX1 : M₂ * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε / 16 := by
    have h1 : M₂ ≤ M₂ + 1 := by linarith
    have h2 : 0 ≤ (1 + period) * (lam + (period - sweepW' D σ₀)) :=
      mul_nonneg (by linarith [hP]) hX0
    have h3 : M₂ * ((1 + period) * (lam + (period - sweepW' D σ₀)))
        ≤ (M₂ + 1) * ((1 + period) * (lam + (period - sweepW' D σ₀))) :=
      mul_le_mul_of_nonneg_right h1 h2
    have h4 : (M₂ + 1) * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε / 16 := by
      linarith [hvelε]
    linarith [h3, h4]
  have hC1 : M₂ * (3 * η + 6 * θ) ≤ 9 * ε / 1024 := by
    have h1 : 3 * η + 6 * θ ≤ 9 * (ε / (1024 * B)) := by
      have ha : 3 * η ≤ 3 * (ε / (1024 * B)) := mul_le_mul_of_nonneg_left hηB (by norm_num)
      have hb : 6 * θ ≤ 6 * (ε / (1024 * B)) := mul_le_mul_of_nonneg_left hθB (by norm_num)
      linarith
    have h5 : M₂ * (9 * (ε / (1024 * B))) ≤ 9 * ε / 1024 := by
      have hq : M₂ / B ≤ 1 := by rw [div_le_one hB0]; linarith [hM₂B]
      have hY : 0 ≤ 9 * ε / 1024 := by positivity
      calc M₂ * (9 * (ε / (1024 * B))) = (9 * ε / 1024) * (M₂ / B) := by ring_nf
        _ ≤ (9 * ε / 1024) * 1 := mul_le_mul_of_nonneg_left hq hY
        _ = 9 * ε / 1024 := by ring
    calc M₂ * (3 * η + 6 * θ) ≤ M₂ * (9 * (ε / (1024 * B))) :=
          mul_le_mul_of_nonneg_left h1 hM₂0
      _ ≤ 9 * ε / 1024 := h5
  refine ⟨θ, θ, widePhaseApprox D lam θ θ σ₀, hθ0, hθL, hθ0, hθL, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_widePhaseApprox D hlam0 hlam4 (ne_of_gt hθ0) (ne_of_gt hθ0)
  · intro t
    exact widePhaseApprox_add_period D hlam0 hlam4 θ θ σ₀ t
  · intro t
    rw [deriv_widePhaseApprox D (ne_of_gt hθ0) hθ0 hlam0 hlam4 (by linarith) (by linarith)]
    exact wf_rateBlur_pos D hlam0 hlam4 hθ0.le hθσlo hθσhi
  · intro t
    have h1 : ‖sweepFam r D lam θ θ σ₀ t - sweepLoopChamfer r D lam σ₀ t‖ ≤ ε / 8 :=
      hδc θ θ hθ0 hθc hθ0 hθc σ₀ t
    have h2 : ‖sweepLoopChamfer r D lam σ₀ t - r (wideSig D lam σ₀ t)‖
        ≤ Cv * (lam * period + (period - sweepW' D σ₀)) ^ 2 :=
      hval lam σ₀ t hlam0 hlam4 hσ₀ hσ₀1.le
    have h4 : ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖ ≤ ε / 16 := by
      have h6 := hlipr (wideSig D lam σ₀ t) (widePhaseApprox D lam θ θ σ₀ t)
      have h7 : |wideSig D lam σ₀ t - widePhaseApprox D lam θ θ σ₀ t| ≤ 2 * (η + 2 * θ) := by
        have h := hψval t
        rwa [abs_sub_comm] at h
      calc ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖
          ≤ M₁ * |wideSig D lam σ₀ t - widePhaseApprox D lam θ θ σ₀ t| := h6
        _ ≤ M₁ * (2 * (η + 2 * θ)) := mul_le_mul_of_nonneg_left h7 hM₁0
        _ ≤ ε / 16 := hη4
    calc ‖sweepFam r D lam θ θ σ₀ t - r (widePhaseApprox D lam θ θ σ₀ t)‖
        ≤ ‖sweepFam r D lam θ θ σ₀ t - sweepLoopChamfer r D lam σ₀ t‖
          + ‖sweepLoopChamfer r D lam σ₀ t - r (wideSig D lam σ₀ t)‖
          + ‖r (wideSig D lam σ₀ t) - r (widePhaseApprox D lam θ θ σ₀ t)‖ := by
          have h8 := wf_norm_sub_le_trans (sweepFam r D lam θ θ σ₀ t)
            (sweepLoopChamfer r D lam σ₀ t) (r (widePhaseApprox D lam θ θ σ₀ t))
          have h9 := wf_norm_sub_le_trans (sweepLoopChamfer r D lam σ₀ t)
            (r (wideSig D lam σ₀ t)) (r (widePhaseApprox D lam θ θ σ₀ t))
          linarith
      _ ≤ ε / 8 + ε / 16 + ε / 16 := by linarith
      _ ≤ ε / 2 := by linarith
  · intro τ
    have hdF : HasDerivAt (fun u : ℝ => sweepFam r D lam θ θ σ₀ u)
        (∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) τ :=
      sweepFam_double_blur_deriv hr D hlam0 (by linarith) (ne_of_gt hθ0) hθ0
        (by linarith) (by linarith)
    have hdψ : deriv (widePhaseApprox D lam θ θ σ₀) τ = wideRateBlur D lam θ θ σ₀ τ :=
      deriv_widePhaseApprox D (ne_of_gt hθ0) hθ0 hlam0 hlam4 (by linarith) (by linarith) τ
    rw [hdF.deriv, hdψ]
    have hΓb : ∀ v u : ℝ, ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)‖ ≤ doubleBlurLam lam Vb Rb (2 * AAb) := by
      intro v u
      exact doubleBlur_chamferVel_bound hlam0 (by linarith)
        (fun x => by simpa only [velocity] using hVb x) hRb hTwb0 (σ₀ - θ * v) (hWb _) (τ - θ * u)
    have hCΓ0 : 0 ≤ doubleBlurLam lam Vb Rb (2 * AAb) :=
      doubleBlurLam_nonneg hlam0 hVb0.le hRb0 hTwb0
    have hVVb : ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ Vb := hVb _
    have hwpos : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 →
        0 < sweepW' D (σ₀ - θ * v) ∧ sweepW' D (σ₀ - θ * v) < period := by
      intro v hv
      obtain ⟨h1, h2⟩ := hσv v hv
      have h := sweepW_pos_lt D ⟨σ₀ - θ * v, h1.le, h2.le⟩ ⟨h1, h2⟩
      rwa [wf_sweepW'_eq D h1.le h2.le]
    have hdev : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |wideSig D lam (σ₀ - θ * v) (τ - θ * u) - widePhaseApprox D lam θ θ σ₀ τ| ≤ 3 * η + 6 * θ := by
      intro v hv u hu
      have hu1 : |u| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩
      have e1 : |wideSig D lam (σ₀ - θ * v) (τ - θ * u) - wideSig D lam σ₀ (τ - θ * u)| ≤ η := hηθ v hv (τ - θ * u)
      have e2 : |wideSig D lam σ₀ (τ - θ * u) - wideSig D lam σ₀ τ| ≤ 2 * θ := by
        have h := hτlip lam σ₀ (τ - θ * u) τ hlam0 hlam4
        have h2 : |τ - θ * u - τ| = θ * |u| := by
          rw [show τ - θ * u - τ = -(θ * u) by ring, abs_neg, abs_mul, abs_of_nonneg hθ0.le]
        rw [h2] at h
        nlinarith [h, hu1, hθ0]
      have e3 : |wideSig D lam σ₀ τ - widePhaseApprox D lam θ θ σ₀ τ| ≤ 2 * (η + 2 * θ) :=
        (abs_sub_comm _ _).trans_le (hψval τ)
      have htri := abs_sub_le (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) (wideSig D lam σ₀ (τ - θ * u)) (widePhaseApprox D lam θ θ σ₀ τ)
      have htri2 := abs_sub_le (wideSig D lam σ₀ (τ - θ * u)) (wideSig D lam σ₀ τ) (widePhaseApprox D lam θ θ σ₀ τ)
      linarith
    have hρpos : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 → ∀ u : ℝ, 0 < wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by
      intro v hv u
      obtain ⟨hw0, hwP⟩ := hwpos v hv
      have hdl : (0:ℝ) < 1 - 2 * lam := by linarith
      have hd2 : (0:ℝ) < 1 / 2 - lam := by linarith
      simp only [wideRho]
      split_ifs
      · exact mul_pos hdl (div_pos (mul_pos (by norm_num) hw0) period_pos)
      · norm_num
      · exact div_pos (mul_pos hdl (by linarith)) (mul_pos period_pos hd2)
      · norm_num
    have hpoint : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ (ε / 2) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by
      intro v hv u hu
      have hρp : 0 < wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := hρpos v hv u
      obtain ⟨hσv0, hσv1⟩ := hσv v hv
      have hVel := hvel lam (σ₀ - θ * v) (τ - θ * u) hlam0 hlam4 hσv0 hσv1
      have hv2 : ‖velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ M₂ * (3 * η + 6 * θ) := by
        have h := hM₂ (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) (widePhaseApprox D lam θ θ σ₀ τ)
        have hd := hdev v hv u hu
        nlinarith [h, hd, hM₂0]
      have h2 : ‖wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (3 * η + 6 * θ)) := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg hρp.le]
        exact mul_le_mul_of_nonneg_left hv2 hρp.le
      have hsplit : lam + (period - sweepW' D (σ₀ - θ * v))
          = (lam + (period - sweepW' D σ₀)) + (sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)) := by ring
      have hΔ : |sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)|
          ≤ 3 * ε / (32 * (M₂ * (1 + period) + 1)) := by
        have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hv.1], hv.2⟩
        have hd : dist (σ₀ - θ * v) σ₀ < δw := by
          rw [Real.dist_eq, show σ₀ - θ * v - σ₀ = -(θ * v) by ring, abs_neg, abs_mul,
            abs_of_nonneg hθ0.le]
          calc θ * |v| ≤ θ * 1 := mul_le_mul_of_nonneg_left hv1 hθ0.le
            _ = θ := mul_one _
            _ < δw := by linarith [hθw, hδw0]
        have h := hδw hd
        rw [Real.dist_eq, abs_sub_comm] at h
        exact le_of_lt h
      have hB1 : M₂ * (1 + period) * (sweepW' D σ₀ - sweepW' D (σ₀ - θ * v)) ≤ 3 * ε / 32 := by
        refine (mul_le_mul_of_nonneg_left (le_abs_self _) hMp).trans ?_
        exact (mul_le_mul_of_nonneg_left hΔ hMp).trans
          (wf_mul_div_le hMp (by positivity))
      have hξ : M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v)))
          + M₂ * (3 * η + 6 * θ) ≤ ε / 2 := by
        rw [hsplit, mul_add]
        linarith [hX1, hB1, hC1, hε]
      have hdecomp : chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
          = (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))) + (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) := by
        rw [sub_add_sub_cancel]
      calc ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖
          = ‖(chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))) + (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))‖ := by
            rw [hdecomp]
        _ ≤ ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u))‖ + ‖wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (wideSig D lam (σ₀ - θ * v) (τ - θ * u)) - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ := norm_add_le _ _
        _ ≤ M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v))) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u))
              + wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (3 * η + 6 * θ)) := add_le_add hVel h2
        _ = wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (M₂ * (1 + period) * (lam + (period - sweepW' D (σ₀ - θ * v)))
              + M₂ * (3 * η + 6 * θ)) := by ring
        _ ≤ wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) * (ε / 2) := mul_le_mul_of_nonneg_left hξ hρp.le
        _ = (ε / 2) * wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) := by ring
    have hpairstuff : Measurable (fun p : ℝ × ℝ => (σ₀ - θ * p.1, τ - θ * p.2)) :=
      (measurable_const.sub (measurable_const.mul measurable_fst)).prod
        (measurable_const.sub (measurable_const.mul measurable_snd))
    have hΓm0 : Measurable (fun p : ℝ × ℝ => chamferVel r D lam p.1 p.2) :=
      wideEnd_measurable_chamferVel_joint hr.continuous (hr.smooth.continuous_deriv (by simp)) D lam
    have hΓm : Measurable (fun p : ℝ × ℝ => chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2)) :=
      hΓm0.comp hpairstuff
    have hρm0 : Measurable (fun p : ℝ × ℝ => wideRhoFun D lam (σ₀ - θ * p.1, τ - θ * p.2)) :=
      (measurable_wideRhoFun D lam).comp hpairstuff
    have hρm : Measurable (fun p : ℝ × ℝ =>
        wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
          (sweepParam (τ - θ * p.2))) := by
      simpa only [wideRhoFun] using hρm0
    have hgm : Measurable (Function.uncurry (fun (v u : ℝ) =>
        chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) :=
      hΓm.sub (hρm.smul measurable_const)
    have hgb : ∀ v u : ℝ, ‖chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
        - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖ ≤ doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb := by
      intro v u
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add (hΓb v u) ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) (hVb _) (norm_nonneg _) hCρ0
    have hρb : ∀ v u : ℝ, |wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
        (sweepParam (τ - θ * u))| ≤ Cρ := fun v u => hCρb (σ₀ - θ * v) (τ - θ * u)
    have hCg0 : 0 ≤ doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb := by
      have h1 := hCΓ0; have h2 := hCρ0; have h3 := hVb0; positivity
    have hΓint : ∀ v : ℝ, IntervalIntegrable
        (fun u : ℝ => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) volume (-1) 1 := by
      intro v
      refine wf_intervalIntegrable_of_global_bound' (C := doubleBlurLam lam Vb Rb (2 * AAb)) ?_ ?_
      · have hmap : Measurable (fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ)) :=
          Measurable.prod (f := fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ))
            measurable_const (measurable_const.sub (measurable_const.mul measurable_id))
        have hΓu : AEStronglyMeasurable
            (fun u : ℝ => chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) volume :=
          (hΓm0.comp hmap).aestronglyMeasurable
        exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hΓu
      · intro u
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        exact wf_sweepBump_mul_bound (hΓb v u) u
    have hVint : ∀ v : ℝ, IntervalIntegrable
        (fun u : ℝ => sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
        volume (-1) 1 := by
      intro v
      refine wf_intervalIntegrable_of_global_bound' (C := Cρ * Vb) ?_ ?_
      · have hmap : Measurable (fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ)) :=
          Measurable.prod (f := fun u : ℝ => ((σ₀ - θ * v, τ - θ * u) : ℝ × ℝ))
            measurable_const (measurable_const.sub (measurable_const.mul measurable_id))
        have hρu : AEStronglyMeasurable (fun u : ℝ => wideRho (sweepW' D (σ₀ - θ * v))
            (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u))) volume :=
          ((measurable_wideRhoFun D lam).comp hmap).aestronglyMeasurable
        refine (continuous_sweepBump.measurable.aestronglyMeasurable).smul ?_
        exact hρu.smul measurable_const.aestronglyMeasurable
      · intro u
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u), norm_smul, Real.norm_eq_abs]
        calc sweepBump u * (|wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v))
              lam (sweepParam (τ - θ * u))| * ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖)
            ≤ 1 * (Cρ * Vb) :=
              mul_le_mul (wf_sweepBump_le_one u)
                (mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) hVVb (norm_nonneg _) hCρ0)
                (by positivity) zero_le_one
          _ = Cρ * Vb := one_mul _
    have hssΓ : StronglyMeasurable (fun v : ℝ =>
        ∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) := by
      have hL : StronglyMeasurable (Function.uncurry
          (fun (v u : ℝ) => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) := by
        have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 •
            chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2)) :=
          (continuous_sweepBump.measurable.comp measurable_snd).smul hΓm
        rw [show Function.uncurry (fun (v u : ℝ) => sweepBump u •
              chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))
            = fun p : ℝ × ℝ => sweepBump p.2 •
              chamferVel r D lam (σ₀ - θ * p.1) (τ - θ * p.2) from rfl]
        exact h.stronglyMeasurable
      have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (v u : ℝ) => sweepBump u • chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) hL
        (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
      have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
          = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)) := by
        funext v
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          Set.uIoc_of_le (by norm_num)]
      rw [hfun] at h2
      exact h2
    have hssV : StronglyMeasurable (fun v : ℝ =>
        ∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
      have hL : StronglyMeasurable (Function.uncurry (fun (v u : ℝ) => sweepBump u •
          (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))) := by
        have h : Measurable (fun p : ℝ × ℝ => sweepBump p.2 •
            (wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
              (sweepParam (τ - θ * p.2)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) :=
          (continuous_sweepBump.measurable.comp measurable_snd).smul (hρm.smul measurable_const)
        rw [show Function.uncurry (fun (v u : ℝ) => sweepBump u •
              (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
            = fun p : ℝ × ℝ => sweepBump p.2 •
              (wideRho (sweepW' D (σ₀ - θ * p.1)) (period - sweepW' D (σ₀ - θ * p.1)) lam
                (sweepParam (τ - θ * p.2)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) from rfl]
        exact h.stronglyMeasurable
      have h2 := MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun (v u : ℝ) => sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) hL
        (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1))
      have hfun : (fun v : ℝ => ∫ u : ℝ, sweepBump u •
            (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
          = (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u •
            (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
        funext v
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          Set.uIoc_of_le (by norm_num)]
      rw [hfun] at h2
      exact h2
    have hΓbd : ∀ v : ℝ, ‖∫ u in (-1 : ℝ)..1, sweepBump u •
        chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)‖ ≤ 2 * doubleBlurLam lam Vb Rb (2 * AAb) := by
      intro v
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := doubleBlurLam lam Vb Rb (2 * AAb)) (fun u _ => ?_)).trans ?_
      · rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        exact wf_sweepBump_mul_bound (hΓb v u) u
      · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
    have hVbd : ∀ v : ℝ, ‖∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
        (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))‖
        ≤ 2 * (Cρ * Vb) := by
      intro v
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Cρ * Vb)
        (fun u _ => ?_)).trans ?_
      · rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u), norm_smul, Real.norm_eq_abs]
        calc sweepBump u * (|wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v))
              lam (sweepParam (τ - θ * u))| * ‖velocity r (widePhaseApprox D lam θ θ σ₀ τ)‖)
            ≤ 1 * (Cρ * Vb) :=
              mul_le_mul (wf_sweepBump_le_one u)
                (mul_le_mul (hCρb (σ₀ - θ * v) (τ - θ * u)) hVVb (norm_nonneg _) hCρ0)
                (by positivity) zero_le_one
          _ = Cρ * Vb := one_mul _
      · rw [show |1 - (-1 : ℝ)| = 2 by norm_num]; linarith
    have hL1 : IntervalIntegrable (fun v : ℝ => sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u •
          chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))) volume (-1) 1 := by
      refine wf_intervalIntegrable_of_global_bound' (C := 2 * doubleBlurLam lam Vb Rb (2 * AAb)) ?_ ?_
      · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hssΓ.aestronglyMeasurable
      · intro v
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
        exact wf_sweepBump_mul_bound (hΓbd v) v
    have hV1 : IntervalIntegrable (fun v : ℝ => sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u • (wideRho (sweepW' D (σ₀ - θ * v))
          (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))))
        volume (-1) 1 := by
      refine wf_intervalIntegrable_of_global_bound' (C := 2 * (Cρ * Vb)) ?_ ?_
      · exact (continuous_sweepBump.measurable.aestronglyMeasurable).smul hssV.aestronglyMeasurable
      · intro v
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
        exact wf_sweepBump_mul_bound (hVbd v) v
    have hkey : (∫ v in (-1 : ℝ)..1, sweepBump v •
          (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)))
        - wideRateBlur D lam θ θ σ₀ τ • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
        = ∫ v in (-1 : ℝ)..1, sweepBump v •
            (∫ u in (-1 : ℝ)..1, sweepBump u •
              (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
                - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                    (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
      have hΛV : wideRateBlur D lam θ θ σ₀ τ • velocity r (widePhaseApprox D lam θ θ σ₀ τ)
          = ∫ v in (-1 : ℝ)..1, sweepBump v •
              (∫ u in (-1 : ℝ)..1, sweepBump u •
                (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                  (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))) := by
        rw [wideRateBlur]
        exact wf_double_scalar_smul sweepBump
          (fun v u => wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
            (sweepParam (τ - θ * u))) (velocity r (widePhaseApprox D lam θ θ σ₀ τ))
      rw [hΛV, ← intervalIntegral.integral_sub hL1 hV1]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      have hinner : (∫ u in (-1 : ℝ)..1, sweepBump u •
            chamferVel r D lam (σ₀ - θ * v) (τ - θ * u))
          - (∫ u in (-1 : ℝ)..1, sweepBump u •
              (wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)))
          = ∫ u in (-1 : ℝ)..1, sweepBump u •
              (chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
                - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
                    (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ)) := by
        rw [← intervalIntegral.integral_sub (hΓint v) (hVint v)]
        exact intervalIntegral.integral_congr (fun u _ => (smul_sub (sweepBump u) _ _).symm)
      rw [← smul_sub, hinner]
    rw [hkey, wideRateBlur]
    exact wf_double_norm_le (g := fun (v u : ℝ) => chamferVel r D lam (σ₀ - θ * v) (τ - θ * u)
          - wideRho (sweepW' D (σ₀ - θ * v)) (period - sweepW' D (σ₀ - θ * v)) lam
              (sweepParam (τ - θ * u)) • velocity r (widePhaseApprox D lam θ θ σ₀ τ))
      (ρ' := fun (v u : ℝ) => wideRho (sweepW' D (σ₀ - θ * v))
        (period - sweepW' D (σ₀ - θ * v)) lam (sweepParam (τ - θ * u)))
      (c := ε / 2) (Cg := doubleBlurLam lam Vb Rb (2 * AAb) + Cρ * Vb) (Cρ' := Cρ)
      hgm hgb hρm hρb hCg0 (by linarith) hpoint

end

end Work.Drive
