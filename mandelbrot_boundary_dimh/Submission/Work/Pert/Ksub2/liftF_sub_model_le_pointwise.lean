import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.ratio_sub_ratio_le
import Submission.Work.Pert.hF_lipschitz_on_ball
import Submission.Work.Pert.exp_alpha_bounds

/-!
# PERT · `Work.Pert.Ksub2.liftF_sub_model_le_pointwise`

The *pointwise* model comparison for the perturbed lift `F_f = liftF u σ α`: this is the same
estimate as `Work.Pert.liftF_sub_model_le`,

  `‖F_f w - (w + hF (τ₀ w)/(1 + τ₀ w · hF (τ₀ w)))‖ ≤ 1000 (D + 1) (η + δ₂)`,

but the hypothesis on `u` is weakened from "`u` is differentiable on `ball 0 ρ` and uniformly
`η`-close to `hF` away from `0`" to the *single point* statement
`‖u (τ_f w) - hF (τ_f w)‖ ≤ η` (together with `‖u 0 - 1‖ ≤ η`).

Indeed the proof of `liftF_sub_model_le` only ever uses the closeness of `u` to `hF` at the single
point `τ = τ_f w = tauC σ α w`; only the auxiliary derivation of the case `τ = 0` used
differentiability of `u` (it produced the closeness at `0` as a limit), and in the pointwise
version `τ = 0` is covered directly by the hypothesis.

The decomposition is the one of `liftF_sub_model_le`: writing `τ = τ_f w`, `τ₀ = τ₀ w`,
`s = sfun u σ α w`, `m = hF τ₀/(1 + τ₀ hF τ₀)`, `A = exp (2πiα) = 1 - σ u 0`, `X = u τ/(u₀ (1 + τ u τ))`,
`Y = m`, one has `liftF u σ α w = w + (2πiα)⁻¹ log (1 - s)` and the exact identity
`-s/(2πiα) = ((A-1)/(2πiα)) X`, so

  `(2πiα)⁻¹ log (1 - s) - m = (2πiα)⁻¹ (log (1-s) + s)
      + [((A-1)/(2πiα) - 1) X + (X - Y)]`,

and the three pieces are bounded by `600 η`, `28 η` and `20 (D+1)(η+δ₂)` respectively.
-/

open Complex Filter

open scoped Topology

set_option maxHeartbeats 4000000

set_option linter.unusedVariables false

namespace Work.Pert.Ksub2

noncomputable section

/-- `‖log (1 + z) - z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2`. -/
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

private lemma norm_two_pi_I_mul (α : ℂ) : ‖(2 * Real.pi * I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
  rw [norm_mul, norm_mul, norm_mul]
  rw [Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

private lemma norm_inv_two_pi_I_mul (α : ℂ) :
    ‖(1 / (2 * Real.pi * I * α) : ℂ)‖ = 1 / (2 * Real.pi * ‖α‖) := by
  rw [norm_div, norm_one, norm_two_pi_I_mul]

private lemma two_pi_I_mul_ne_zero {α : ℂ} (hα : α ≠ 0) : (2 * Real.pi * I * α : ℂ) ≠ 0 := by
  intro h
  have h1 := norm_two_pi_I_mul α
  rw [h, norm_zero] at h1
  have h2 : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h3 : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem liftF_sub_model_le_pointwise {u hF : ℂ → ℂ} {σ α w : ℂ} {ρ D η δ₁ δ₂ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hD : 0 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1 / 1000)
    (hδ1 : ‖MandelDim.tau0 w‖ ≤ δ₁) (hδ1' : δ₁ ≤ 1 / 64)
    (hδ2 : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ δ₂) (hδ2' : 0 ≤ δ₂)
    (hδsum : δ₁ + δ₂ ≤ ρ / 4)
    (hFd : DifferentiableOn ℂ hF (Metric.ball 0 ρ))
    (hFl : ∀ z ∈ Metric.ball 0 ρ, ‖deriv hF z‖ ≤ D)
    (hFb : ∀ z ∈ Metric.ball 0 ρ, ‖hF z‖ ≤ 3 / 2)
    (hut : ‖u (Work.Pert.tauC σ α w) - hF (Work.Pert.tauC σ α w)‖ ≤ η)
    (hu0 : ‖u 0 - 1‖ ≤ η)
    (hα : α ≠ 0) (hαη : ‖α‖ ≤ η) (hαπ : ‖α‖ ≤ 1 / (2 * Real.pi))
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hw : w ≠ 0) (hwu : ‖α‖ * ‖w‖ ≤ 1 / 2) :
    ‖Work.Pert.liftF u σ α w
        - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖
      ≤ 1000 * (D + 1) * (η + δ₂) := by
  set t : ℂ := Work.Pert.tauC σ α w with ht
  set t0 : ℂ := MandelDim.tau0 w with ht0
  set u0 : ℂ := u 0 with hu0e
  set h0 : ℂ := hF t0 with hh0e
  set hFt : ℂ := hF t with hhFte
  set s : ℂ := sfun u σ α w with hse
  set A : ℂ := Complex.exp (2 * Real.pi * I * α) with hAe
  -- ## basic size facts
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hδ1nn : 0 ≤ δ₁ := le_trans (norm_nonneg _) hδ1
  have ht0_le : ‖t0‖ ≤ δ₁ := by rw [ht0]; exact hδ1
  have ht_le : ‖t‖ ≤ δ₁ + δ₂ := by
    rw [ht]
    have h := norm_add_le (Work.Pert.tauC σ α w - MandelDim.tau0 w) (MandelDim.tau0 w)
    simp only [sub_add_cancel] at h
    linarith
  have ht16 : ‖t‖ ≤ 1 / 16 := by linarith
  have ht064 : ‖t0‖ ≤ 1 / 64 := le_trans ht0_le hδ1'
  have htmem : t ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  have ht0mem : t0 ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
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
      simpa [hAe] using (exp_alpha_bounds hα h2πα).2.1
    linarith
  -- ## `u` versus `hF` at `t` (the single point hypothesis)
  have htA : ‖u t - hFt‖ ≤ η := by
    rw [hhFte, ht]
    exact hut
  have huτ : ‖u t‖ ≤ 3 / 2 + η := by
    have h1 : ‖u t‖ ≤ ‖u t - hF t‖ + ‖hF t‖ := by
      have h := norm_add_le (u t - hF t) (hF t)
      simpa using h
    have h2 : ‖hF t‖ ≤ 3 / 2 := hFb t htmem
    have h3 : ‖u t - hF t‖ ≤ η := by rw [← hhFte]; exact htA
    linarith
  have hhFt_le : ‖hFt‖ ≤ 3 / 2 := by rw [hhFte]; exact hFb t htmem
  have hh0_le : ‖h0‖ ≤ 3 / 2 := by rw [hh0e]; exact hFb t0 ht0mem
  have ht_norm : ‖hFt - h0‖ ≤ D * δ₂ := by
    have h1 : ‖hF t - hF t0‖ ≤ D * ‖t - t0‖ :=
      hF_lipschitz_on_ball hρ hFd hFl htmem ht0mem
    have h2 : ‖t - t0‖ ≤ δ₂ := by rw [ht, ht0]; exact hδ2
    rw [hhFte, hh0e]
    calc ‖hF t - hF t0‖ ≤ D * ‖t - t0‖ := h1
      _ ≤ D * δ₂ := mul_le_mul_of_nonneg_left h2 hD
  -- ## denominators
  have htt_u : ‖t * u t‖ ≤ 1 / 8 := by
    rw [norm_mul]
    have h := mul_le_mul ht16 huτ (norm_nonneg (u t)) (by norm_num)
    nlinarith [h]
  have hden : 7 / 8 ≤ ‖1 + t * u t‖ := by
    have h := norm_add_le ((1 : ℂ) + t * u t) (-(t * u t))
    have h' : (1 : ℝ) ≤ ‖(1 : ℂ) + t * u t‖ + ‖-(t * u t)‖ := by simpa using h
    rw [norm_neg] at h'
    linarith
  have hdenne : 1 + t * u t ≠ 0 := by
    intro hh
    have h : ‖(1 : ℂ) + t * u t‖ = 0 := by rw [hh, norm_zero]
    linarith
  have ht0h0 : ‖t0 * h0‖ ≤ 3 / 128 := by
    rw [norm_mul]
    have h := mul_le_mul ht064 hh0_le (norm_nonneg h0) (by norm_num)
    nlinarith [h]
  have hden0 : 125 / 128 ≤ ‖1 + t0 * h0‖ := by
    have h := norm_add_le ((1 : ℂ) + t0 * h0) (-(t0 * h0))
    have h' : (1 : ℝ) ≤ ‖(1 : ℂ) + t0 * h0‖ + ‖-(t0 * h0)‖ := by simpa using h
    rw [norm_neg] at h'
    linarith
  have hdenne0 : 1 + t0 * h0 ≠ 0 := by
    intro hh
    have h : ‖(1 : ℂ) + t0 * h0‖ = 0 := by rw [hh, norm_zero]
    linarith
  have hu0ne : u0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu0n
    norm_num at hu0n
  -- ## the bound on `s`
  have hs_eq : s = σ * u t / (1 + t * u t) := by
    rw [hse]
    simp only [sfun]
    rw [← ht]
  have hs_le : ‖s‖ ≤ 60 * ‖α‖ := by
    rw [hs_eq, norm_div, norm_mul]
    have hnum : ‖σ‖ * ‖u t‖ ≤ 60 * ‖α‖ * (7 / 8) := by
      have h1 : ‖σ‖ * ‖u t‖ ≤ (8 * Real.pi * ‖α‖) * (3 / 2 + η) :=
        mul_le_mul hσbound huτ (norm_nonneg _) (by positivity)
      have h2 : (8 * Real.pi * ‖α‖) * (3 / 2 + η) ≤ 60 * ‖α‖ * (7 / 8) := by
        have hkey : (8 * Real.pi) * (3 / 2 + η) ≤ 60 * (7 / 8) := by
          nlinarith [Real.pi_le_four, Real.pi_pos, hη]
        nlinarith [hkey, norm_nonneg α]
      linarith
    calc (‖σ‖ * ‖u t‖) / ‖1 + t * u t‖
        ≤ (60 * ‖α‖ * (7 / 8)) / (7 / 8) :=
          div_le_div₀ (by positivity) hnum (by norm_num) hden
      _ = 60 * ‖α‖ := by ring
  have hs_half : ‖s‖ ≤ 1 / 2 := by
    have h : 60 * ‖α‖ ≤ 60 * η := mul_le_mul_of_nonneg_left hαη (by norm_num)
    linarith
  -- ## piece 1: the logarithm
  have hlog : ‖Complex.log (1 - s) + s‖ ≤ ‖s‖ ^ 2 := by
    have h := norm_log_one_add_sub_self_le_sq (z := -s) (by rwa [norm_neg])
    rw [norm_neg] at h
    simpa only [sub_eq_add_neg, neg_neg] using h
  have ht1 : ‖(1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)‖ ≤ 600 * η := by
    rw [norm_mul, norm_inv_two_pi_I_mul]
    have h1 : ‖Complex.log (1 - s) + s‖ ≤ (60 * ‖α‖) ^ 2 :=
      le_trans hlog (pow_le_pow_left₀ (norm_nonneg _) hs_le 2)
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
  -- ## piece 2: the exponential remainder
  have hψle : ‖(A - 1) / (2 * Real.pi * I * α) - 1‖ ≤ 8 * ‖α‖ := by
    have h1 : (A - 1) / (2 * Real.pi * I * α) - 1
        = (A - 1 - 2 * Real.pi * I * α) / (2 * Real.pi * I * α) := by
      rw [div_sub_one (two_pi_I_mul_ne_zero hα)]
    rw [h1, norm_div, norm_two_pi_I_mul]
    have h2 : ‖A - 1 - 2 * Real.pi * I * α‖ ≤ 4 * Real.pi ^ 2 * ‖α‖ ^ 2 := by
      simpa [hAe] using (exp_alpha_bounds hα h2πα).1
    have h3 : 4 * Real.pi ^ 2 * ‖α‖ ^ 2 / (2 * Real.pi * ‖α‖) ≤ 8 * ‖α‖ := by
      have hπ : Real.pi ≤ 4 := Real.pi_le_four
      rw [div_le_iff₀ (by positivity)]
      have hπ4 : (4 : ℝ) * Real.pi ^ 2 ≤ 16 * Real.pi := by
        calc 4 * Real.pi ^ 2 = (4 * Real.pi) * Real.pi := by ring
          _ ≤ (4 * Real.pi) * 4 := mul_le_mul_of_nonneg_left hπ (by positivity)
          _ = 16 * Real.pi := by ring
      calc 4 * Real.pi ^ 2 * ‖α‖ ^ 2 ≤ 16 * Real.pi * ‖α‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hπ4 (sq_nonneg ‖α‖)
        _ = 8 * ‖α‖ * (2 * Real.pi * ‖α‖) := by ring
    calc ‖A - 1 - 2 * Real.pi * I * α‖ / (2 * Real.pi * ‖α‖)
        ≤ (4 * Real.pi ^ 2 * ‖α‖ ^ 2) / (2 * Real.pi * ‖α‖) := by
          gcongr
      _ ≤ 8 * ‖α‖ := h3
  have hX : ‖u t / (u0 * (1 + t * u t))‖ ≤ 7 / 2 := by
    rw [norm_div, norm_mul]
    have hden' : (1 / 2) * (7 / 8) ≤ ‖u0‖ * ‖1 + t * u t‖ :=
      mul_le_mul hu0n hden (by norm_num) (norm_nonneg u0)
    have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ 3 / 2 + η) huτ
      (by norm_num : (0 : ℝ) < 1 / 2 * (7 / 8)) hden'
    have hb : (3 / 2 + η) / (1 / 2 * (7 / 8)) ≤ 7 / 2 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [hη1]
    linarith [h, hb]
  have hψX : ‖((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))‖
      ≤ 28 * η := by
    rw [norm_mul]
    have h1 : ‖(A - 1) / (2 * Real.pi * I * α) - 1‖ * ‖u t / (u0 * (1 + t * u t))‖
        ≤ (8 * ‖α‖) * (7 / 2) :=
      mul_le_mul hψle hX (norm_nonneg _) (by positivity)
    have h2 : 8 * ‖α‖ * (7 / 2) ≤ 28 * η := by nlinarith [hαη, norm_nonneg α]
    linarith
  -- ## piece 3: the ratio comparison
  have hXY : ‖u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0)‖
      ≤ 20 * (D + 1) * (η + δ₂) :=
    ratio_sub_ratio_le (t := t) (ut := u t) (t0 := t0) (u0 := u0) (hFt := hFt) (h0 := h0)
      hD hη hη1 hδ2' hu0n (by rw [hu0e]; exact hu0) htA ht_norm
      (by rw [ht, ht0]; exact hδ2) ht16 ht064 hh0_le hhFt_le huτ
  -- ## the algebraic decomposition
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
    have h1 : ‖(1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)
        + (((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))
          + (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0)))‖
        ≤ ‖(1 / (2 * Real.pi * I * α)) * (Complex.log (1 - s) + s)‖
          + ‖((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))
            + (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0))‖ :=
      norm_add_le _ _
    have h2 : ‖((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))
        + (u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0))‖
        ≤ ‖((A - 1) / (2 * Real.pi * I * α) - 1) * (u t / (u0 * (1 + t * u t)))‖
          + ‖u t / (u0 * (1 + t * u t)) - h0 / (1 + t0 * h0)‖ :=
      norm_add_le _ _
    have hD1 : (0 : ℝ) ≤ D + 1 := by linarith
    have hscale : η ≤ (D + 1) * (η + δ₂) := by
      have : η ≤ η + δ₂ := by linarith
      nlinarith
    linarith [h1, h2, ht1, hψX, hXY]
  -- ## transport to the statement
  have hlift : Work.Pert.liftF u σ α w
      = w + (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) := by
    simp only [liftF]
    rw [← hse]
  have hsub : w + (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - (w + h0 / (1 + t0 * h0))
      = (1 / (2 * Real.pi * I * α)) * Complex.log (1 - s) - h0 / (1 + t0 * h0) := by ring
  rw [hlift, hsub]
  exact hfinal

end

end Work.Pert.Ksub2
