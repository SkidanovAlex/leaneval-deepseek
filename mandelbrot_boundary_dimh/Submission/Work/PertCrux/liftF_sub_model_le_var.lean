import Mathlib
import Submission.Work.Pert.liftF_sub_model_le
import Submission.Work.Pert.hF_lipschitz_on_ball
import Submission.Work.PertCrux.exp_remainder_mul_le
import Submission.Work.PertCrux.norm_sfun_div_le
import Submission.Work.PertCrux.norm_X_le
import Submission.Work.PertCrux.norm_sub_zero_le_of_punctured

/-!
# PERTCRUX · `Work.PertCrux.liftF_sub_model_le_var`

The *model comparison* for the perturbed lift `F_f = liftF u σ α` in the form needed by the
PERT area, where the perturbed coordinate `τ_f w = σ/(1 - exp (-2πiαw))` and the model coordinate
`τ₀ w = -1/w` are known to lie in the balls of radii `ρu` resp. `ρh` (with `ρu ≤ ρh ≤ 1/4`),
rather than being controlled through the pair `(δ₁, δ₂)` with `δ₁ + δ₂ ≤ ρ/4` as in
`Work.Pert.liftF_sub_model_le`:

  `‖F_f w - (w + hF (τ₀ w)/(1 + τ₀ w · hF (τ₀ w)))‖ ≤ 1000 (D + 1) (η + δ₂)`.

Here `D` bounds `‖hF'‖` on `ball 0 ρh`, `hF` is bounded by `3/2` there, `u` is `η`-close to `hF`
on the punctured ball `ball 0 ρu` (and `u 0` is `η`-close to `1`), and
`‖τ_f w - τ₀ w‖ ≤ δ₂`, `‖τ_f w‖ ≤ 1/16`, `‖τ₀ w‖ ≤ 1/64`.

## Proof

Identical in content to `Work.Pert.liftF_sub_model_le`, but this time the memberships
`τ_f w ∈ ball 0 ρu ⊆ ball 0 ρh` and `τ₀ w ∈ ball 0 ρh` are hypotheses, which is exactly what the
old proof derives from `δ₁ + δ₂ ≤ ρ/4`; and closeness of `u` to `hF` is available at the point
`τ_f w` *except* possibly at `τ_f w = 0`, where it is recovered by continuity of `u - hF` at `0`
(`Work.PertCrux.norm_sub_zero_le_of_punctured`).

Writing `τ = τ_f w`, `τ₀ = τ₀ w`, `s = sfun u σ α w`, `m = hF τ₀/(1 + τ₀ hF τ₀)`,
`A = exp (2πiα) = 1 - σ u 0`, `X = u τ/(u₀ (1 + τ u τ))`, one has
`liftF u σ α w = w + (2πiα)⁻¹ log (1 - s)` and the exact identity
`-s/(2πiα) = ((A-1)/(2πiα)) X`, so

  `(2πiα)⁻¹ log (1 - s) - m = (2πiα)⁻¹ (log (1-s) + s)
      + [((A-1)/(2πiα) - 1) X + (X - m)]`,

and the three pieces are bounded by `600 η`, `28 η` and `20 (D+1)(η+δ₂)` respectively
(the first is the private `log_remainder_le_local` below, the second is
`Work.PertCrux.exp_remainder_mul_le`, the third is `Work.Pert.ratio_sub_ratio_le`).

Supporting estimates proved alongside (all `Work.PertCrux`): `norm_sfun_div_le`, `norm_X_le`,
`exp_remainder_mul_le`, `norm_sub_zero_le_of_punctured`.
-/

open Complex

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.PertCrux

noncomputable section

/-- `‖log (1 + z) - z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2` (the quadratic remainder of the principal
logarithm). -/
private lemma norm_log_one_add_sub_self_le_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h1 : ‖z‖ < 1 := by linarith
  have h2 := Complex.norm_log_one_add_sub_self_le h1
  have h3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖z‖)
    linarith
  linarith

/-- `‖(2πiα)⁻¹‖ = 1/(2π‖α‖)`. -/
private lemma norm_inv_two_pi_I_mul (α : ℂ) :
    ‖(1 / (2 * Real.pi * I * α) : ℂ)‖ = 1 / (2 * Real.pi * ‖α‖) := by
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_mul]
  rw [Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

/-- **Piece 1 of the model comparison** (the logarithm): for `‖s‖ ≤ 60‖α‖`, `‖α‖ ≤ η ≤ 1/1000`
and `α ≠ 0`, `‖(2πiα)⁻¹ (log (1 - s) + s)‖ ≤ 600 η`.  This is
`Work.PertCrux.log_remainder_le`; it is reproduced here privately so that this module does not
depend on a module under construction. -/
private lemma log_remainder_le_local {s α : ℂ} {η : ℝ}
    (hα : α ≠ 0) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hαη : ‖α‖ ≤ η) (hs : ‖s‖ ≤ 60 * ‖α‖) :
    ‖(1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)‖ ≤ 600 * η := by
  have hs_half : ‖s‖ ≤ 1 / 2 := by
    have h : 60 * ‖α‖ ≤ 60 * η := mul_le_mul_of_nonneg_left hαη (by norm_num)
    linarith
  have hlog : ‖Complex.log (1 - s) + s‖ ≤ ‖s‖ ^ 2 := by
    have h := norm_log_one_add_sub_self_le_sq (z := -s) (by rwa [norm_neg])
    rw [norm_neg] at h
    simpa only [sub_eq_add_neg, neg_neg] using h
  rw [norm_mul, norm_inv_two_pi_I_mul]
  have h1 : ‖Complex.log (1 - s) + s‖ ≤ (60 * ‖α‖) ^ 2 :=
    le_trans hlog (pow_le_pow_left₀ (norm_nonneg _) hs 2)
  have h2 : (1 / (2 * Real.pi * ‖α‖)) * (60 * ‖α‖) ^ 2 ≤ 600 * η := by
    have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
    have hαnn : 0 ≤ ‖α‖ := norm_nonneg α
    have hsq : ‖α‖ ^ 2 ≤ η * ‖α‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hαη hαnn
    have hnn : (0 : ℝ) ≤ η * ‖α‖ := mul_nonneg hη.le hαnn
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hsq1 : (60 * ‖α‖) ^ 2 ≤ 3600 * (η * ‖α‖) := by
      have h : (60 * ‖α‖) ^ 2 = 3600 * (‖α‖ ^ 2) := by ring
      rw [h]; linarith
    have hsq2 : 3600 * (η * ‖α‖) ≤ 600 * η * (2 * Real.pi * ‖α‖) := by
      have hπ' : (3600 : ℝ) ≤ 600 * (2 * Real.pi) := by nlinarith
      calc 3600 * (η * ‖α‖) ≤ (600 * (2 * Real.pi)) * (η * ‖α‖) :=
            mul_le_mul_of_nonneg_right hπ' hnn
        _ = 600 * η * (2 * Real.pi * ‖α‖) := by ring
    linarith
  calc (1 / (2 * Real.pi * ‖α‖)) * ‖Complex.log (1 - s) + s‖
      ≤ (1 / (2 * Real.pi * ‖α‖)) * (60 * ‖α‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 600 * η := h2


theorem liftF_sub_model_le_var {u hF : ℂ → ℂ} {σ α w : ℂ} {ρu ρh D η δ₂ : ℝ}
    (hρu : 0 < ρu) (hρh : 0 < ρh) (hρuh : ρu ≤ ρh) (hρh4 : ρh ≤ 1 / 4)
    (hD : 0 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1 / 1000)
    (htu : Work.Pert.tauC σ α w ∈ Metric.ball 0 ρu)
    (ht0 : MandelDim.tau0 w ∈ Metric.ball 0 ρh)
    (ht16 : ‖Work.Pert.tauC σ α w‖ ≤ 1 / 16)
    (ht064 : ‖MandelDim.tau0 w‖ ≤ 1 / 64)
    (hδ2 : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ δ₂) (hδ2' : 0 ≤ δ₂)
    (hFd : DifferentiableOn ℂ hF (Metric.ball 0 ρh))
    (hFl : ∀ z ∈ Metric.ball 0 ρh, ‖deriv hF z‖ ≤ D)
    (hFb : ∀ z ∈ Metric.ball 0 ρh, ‖hF z‖ ≤ 3 / 2)
    (hu : DifferentiableOn ℂ u (Metric.ball 0 ρu))
    (huc : ∀ z ∈ Metric.ball 0 ρu, z ≠ 0 → ‖u z - hF z‖ ≤ η)
    (hu0 : ‖u 0 - 1‖ ≤ η)
    (hα : α ≠ 0) (hαη : ‖α‖ ≤ η) (hαπ : ‖α‖ ≤ 1 / (2 * Real.pi))
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hw : w ≠ 0) (hwu : ‖α‖ * ‖w‖ ≤ 1 / 2) :
    ‖Work.Pert.liftF u σ α w
        - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖
      ≤ 1000 * (D + 1) * (η + δ₂) := by
  set t : ℂ := Work.Pert.tauC σ α w with ht_def
  set t0 : ℂ := MandelDim.tau0 w with ht0_def
  set u0 : ℂ := u 0 with hu0e
  set h0 : ℂ := hF t0 with hh0e
  set hFt : ℂ := hF t with hhFte
  set s : ℂ := Work.Pert.sfun u σ α w with hse
  set A : ℂ := Complex.exp (2 * Real.pi * I * α) with hAe
  -- ## basic size facts
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have htmem_u : t ∈ Metric.ball 0 ρu := by rw [ht_def]; exact htu
  have htlt_u : ‖t‖ < ρu := by
    have h := htmem_u
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  have htmem : t ∈ Metric.ball 0 ρh := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le htlt_u hρuh
  have ht0mem : t0 ∈ Metric.ball 0 ρh := by rw [ht0_def]; exact ht0
  have ht16' : ‖t‖ ≤ 1 / 16 := by rw [ht_def]; exact ht16
  have ht064' : ‖t0‖ ≤ 1 / 64 := by rw [ht0_def]; exact ht064
  have h2πα : 2 * Real.pi * ‖α‖ ≤ 1 := by
    have h1 : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * η :=
      mul_le_mul_of_nonneg_left hαη (by positivity)
    have h2 : 2 * Real.pi * η ≤ 2 * Real.pi * (1 / 1000) :=
      mul_le_mul_of_nonneg_left hη1 (by positivity)
    have h3 : 2 * Real.pi * (1 / 1000) ≤ 1 := by nlinarith [Real.pi_le_four]
    linarith
  have hu0n : 1 / 2 ≤ ‖u0‖ := by
    have h : ‖u0 - 1‖ ≤ η := by rw [hu0e]; exact hu0
    have h2 := abs_norm_sub_norm_le u0 (1 : ℂ)
    rw [norm_one, abs_le] at h2
    linarith
  have hσu : σ * u0 = 1 - A := by rw [hu0e, hAe]; linear_combination -hnorm
  have hσbound : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
    have h1 : ‖σ‖ * (1 / 2) ≤ ‖σ * u0‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hu0n (norm_nonneg σ)
    rw [hσu, norm_sub_rev] at h1
    have h2 : ‖A - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
      simpa [hAe] using (Work.Pert.exp_alpha_bounds hα h2πα).2.1
    linarith
  -- ## `u` versus `hF` at `t`, including the case `t = 0`
  have hcont : ContinuousAt (fun z => u z - hF z) 0 :=
    ((hu.differentiableAt (Metric.ball_mem_nhds 0 hρu)).sub
      (hFd.differentiableAt (Metric.ball_mem_nhds 0 hρh))).continuousAt
  have hψ0 : ‖u 0 - hF 0‖ ≤ η := norm_sub_zero_le_of_punctured hρu hcont huc
  have hψt : ‖u t - hF t‖ ≤ η := by
    by_cases ht0' : t = 0
    · rw [ht0']; exact hψ0
    · exact huc t htmem_u ht0'
  have htA : ‖u t - hFt‖ ≤ η := by rw [hhFte]; exact hψt
  have huτ : ‖u t‖ ≤ 3 / 2 + η := by
    have h1 : ‖u t‖ ≤ ‖u t - hF t‖ + ‖hF t‖ := by
      have h := norm_add_le (u t - hF t) (hF t)
      simpa using h
    have h2 : ‖hF t‖ ≤ 3 / 2 := hFb t htmem
    linarith
  have hhFt_le : ‖hFt‖ ≤ 3 / 2 := by rw [hhFte]; exact hFb t htmem
  have hh0_le : ‖h0‖ ≤ 3 / 2 := by rw [hh0e]; exact hFb t0 ht0mem
  have ht_norm : ‖hFt - h0‖ ≤ D * δ₂ := by
    have h1 : ‖hF t - hF t0‖ ≤ D * ‖t - t0‖ :=
      Work.Pert.hF_lipschitz_on_ball hρh hFd hFl htmem ht0mem
    have h2 : ‖t - t0‖ ≤ δ₂ := by rw [ht_def, ht0_def]; exact hδ2
    rw [hhFte, hh0e]
    calc ‖hF t - hF t0‖ ≤ D * ‖t - t0‖ := h1
      _ ≤ D * δ₂ := mul_le_mul_of_nonneg_left h2 hD
  -- ## the bound on `s`
  have hs_eq : s = σ * u t / (1 + t * u t) := by
    rw [hse]
    simp only [Work.Pert.sfun]
    rw [← ht_def]
  have hs_le : ‖s‖ ≤ 60 * ‖α‖ := by
    rw [hs_eq]
    exact norm_sfun_div_le hη1 hσbound huτ ht16'
  -- ## piece 1: the logarithm
  have ht1 : ‖(1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)‖ ≤ 600 * η :=
    log_remainder_le_local hα hη hη1 hαη hs_le
  -- ## piece 2: the exponential remainder
  have hX : ‖u t / (u0 * (1 + t * u t))‖ ≤ 7 / 2 := norm_X_le hη hη1 hu0n huτ ht16'
  have hψX : ‖((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))‖
      ≤ 28 * η := by
    have h := exp_remainder_mul_le (X := u t / (u0 * (1 + t * u t))) hα hη hη1 hαη hX
    rw [← hAe] at h
    exact h
  -- ## piece 3: the ratio comparison
  have hXY : ‖u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0)‖
      ≤ 20 * (D + 1) * (η + δ₂) :=
    Work.Pert.ratio_sub_ratio_le (t := t) (ut := u t) (t0 := t0) (u0 := u0) (hFt := hFt) (h0 := h0)
      hD hη hη1 hδ2' hu0n (by rw [hu0e]; exact hu0) htA ht_norm
      (by rw [ht_def, ht0_def]; exact hδ2) ht16' ht064' hh0_le hhFt_le huτ
  -- ## the algebraic decomposition
  have hu0ne : u0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu0n
    norm_num at hu0n
  have hσ_eq : σ = (1 - A) / u0 := by
    rw [eq_div_iff hu0ne]; linear_combination hσu
  have hkey : -s / (2 * Real.pi * I * α)
      = ((A - 1) / (2 * Real.pi * I * α)) * (u t / (u0 * (1 + t * u t))) := by
    rw [hs_eq, hσ_eq]
    field_simp
    ring
  have hmain : (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - h0 / (1 + t0 * h0)
      = (1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)
        + (((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))
          + (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0))) := by
    linear_combination hkey
  have hfinal : ‖(1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - h0 / (1 + t0 * h0)‖
      ≤ 1000 * (D + 1) * (η + δ₂) := by
    rw [hmain]
    have h1 := norm_add_le ((1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s))
      (((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))
        + (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0)))
    have h2 := norm_add_le (((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t))))
      (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0))
    have hscale : η ≤ (D + 1) * (η + δ₂) := by
      have : η ≤ η + δ₂ := by linarith
      nlinarith
    linarith [h1, h2, ht1, hψX, hXY]
  -- ## transport to the statement
  have hlift : Work.Pert.liftF u σ α w
      = w + (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) := by
    simp only [Work.Pert.liftF]
    rw [← hse]
  have hsub : w + (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - (w + h0 / (1 + t0 * h0))
      = (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - h0 / (1 + t0 * h0) := by ring
  rw [hlift, hsub]
  exact hfinal

end

end Work.PertCrux
