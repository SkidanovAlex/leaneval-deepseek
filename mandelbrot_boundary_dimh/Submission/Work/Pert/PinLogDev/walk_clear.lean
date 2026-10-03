import Mathlib
import Submission.Work.Pert.PinLogDev.anchor_walk
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.PinAux2
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.PinLogDev.wc_margA_anchor_ge
import Submission.Work.Pert.PinLogDev.wc_Xc_axis_landing
import Submission.Work.Pert.PinLogDev.wc_Xc_axis_norm_pair
import Submission.Work.Pert.PinLogDev.wc_margB_axis_ge

set_option maxHeartbeats 4000000

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-- `log (X + 1) ≤ 1 + log X` for `X ≥ 1`. -/
theorem log_succ_le_one_add_log {X : ℝ} (hX : 1 ≤ X) : Real.log (X + 1) ≤ 1 + Real.log X := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have h1 : Real.log (X + 1) ≤ Real.log (2 * X) := by
    refine Real.log_le_log (by linarith only [hX0]) ?_
    linarith only [hX]
  have h2 : Real.log (2 * X) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (ne_of_gt hX0)
  have h3 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  linarith only [h1, h2, h3]

/-- `2 c · log (M / x) ≤ M - x` when `0 < x`, `2c ≤ x` and `x ≤ M`. -/
theorem two_mul_log_div_le {c x M : ℝ} (hc : 0 ≤ c) (hx0 : 0 < x) (hx : 2 * c ≤ x)
    (hxM : x ≤ M) : 2 * c * Real.log (M / x) ≤ M - x := by
  have hMpos : 0 < M := lt_of_lt_of_le hx0 hxM
  have h1 : Real.log (M / x) ≤ (M - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hMpos hx0)
    have h2 : M / x - 1 = (M - x) / x := by field_simp
    linarith only [h, h2]
  have h2 : 2 * c * Real.log (M / x) ≤ 2 * c * ((M - x) / x) :=
    mul_le_mul_of_nonneg_left h1 (by linarith only [hc])
  have h3 : 2 * c * ((M - x) / x) ≤ M - x := by
    have h4 : 2 * c / x ≤ 1 := by
      rw [div_le_one hx0]; exact hx
    have h5 : (2 * c / x) * (M - x) ≤ 1 * (M - x) :=
      mul_le_mul_of_nonneg_right h4 (by linarith only [hx0, hxM])
    calc 2 * c * ((M - x) / x) = (2 * c / x) * (M - x) := by ring
      _ ≤ 1 * (M - x) := h5
      _ = M - x := by ring
  linarith only [h2, h3]


theorem walk_clear {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) (Rd : ℝ) (hRd : 0 < Rd) :
    ∃ (X₁ Ms Bn : ℝ), 0 < X₁ ∧ 0 < Ms ∧ Rd ≤ X₁ ∧ X₁ + 1 ≤ Ms ∧ d.ξ₀ + 1 < X₁ ∧ 0 ≤ Bn ∧
      ∀ {α : ℂ}, MandelDim.InF1 α →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        ∀ {M : ℝ}, Ms ≤ M → ‖α‖ * M ≤ 1 / 2 →
        Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
        ∃ n : ℕ, X₁ ≤ M - n ∧ M - n ≤ X₁ + 1 ∧
          (∀ j ≤ n, Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α) ∧
          (∀ j < n, Work.Pert.F0f f₀ (Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ))
              = Work.Pert.Xc d ((-((M - (j : ℝ) - 1 : ℝ)) : ℂ))) ∧
          (∀ j < n, ‖Work.Pert.F0f f₀ (Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ))
              - (Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ) + 1)‖ ≤ 1 / 32) ∧
          (∀ j ≤ n, Rd ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ))) ∧
          (∀ j ≤ n, Rd ≤ Work.Pert.margB Ξ α (Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ))) ∧
          (∀ j ≤ n, ‖α‖ * ‖Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ)‖ ≤ 2 / 3) ∧
          (∀ j ≤ n, 64 ≤ ‖Work.Pert.Xc d ((-((M - (j : ℝ)) : ℝ)) : ℂ)‖) ∧
          ‖Work.Pert.Xc d ((-((M - (n : ℝ)) : ℝ)) : ℂ) + (((M - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn ∧
          X₁ / 2 ≤ -(Work.Pert.Xc d ((-((M - (n : ℝ)) : ℝ)) : ℂ)).re ∧
          (Work.Pert.Xc d ((-((M - (n : ℝ)) : ℝ)) : ℂ)).re < -Ξ := by
  obtain ⟨a, b, R, hRpos, hRξ, hRexp, hasym⟩ := exists_Xc_axis_asym d
  obtain ⟨R₀, K₀, K₁, hR₀pos, hK₀0, hK₁0, hwalkmain⟩ := anchor_walk d Ξ hΞ
  set c : ℝ := ‖a‖ with hc
  set cb : ℝ := ‖b‖ with hcb
  set Kk : ℝ := |a.re| + |a.im| with hKk
  set Ch : ℝ := 2 * Kk * Real.pi + |b.re| + |b.im| + Ξ + 4 with hCh
  set μ : ℝ := max 1 (Rd + R + R₀ + Ξ + c + cb + Kk + Ch + K₀ + K₁ + 100) with hμ
  set X₁ : ℝ := (10 : ℝ) ^ 8 * μ ^ 4 with hX₁
  set Ms : ℝ := (10 : ℝ) ^ 10 * μ ^ 8 with hMs
  set Bn : ℝ := c * Real.log (X₁ + 1) + cb + 1 with hBn
  have hμ1 : 1 ≤ μ := le_max_left _ _
  have hμsum : Rd + R + R₀ + Ξ + c + cb + Kk + Ch + K₀ + K₁ + 100 ≤ μ := le_max_right _ _
  have hμpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ1
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg a
  have hcb0 : 0 ≤ cb := by rw [hcb]; exact norm_nonneg b
  have hKk0 : 0 ≤ Kk := by rw [hKk]; positivity
  have hKk0' : 0 ≤ |a.re| + |a.im| := by positivity
  have hΞ0 : 0 ≤ Ξ := by linarith only [hΞ, Real.pi_pos]
  have hbre : |b.re| ≤ cb := by rw [hcb]; exact Complex.abs_re_le_norm b
  have hbim : |b.im| ≤ cb := by rw [hcb]; exact Complex.abs_im_le_norm b
  have hCh0 : 0 ≤ Ch := by
    rw [hCh]
    have h1 : 0 ≤ 2 * Kk * Real.pi := mul_nonneg (mul_nonneg (by norm_num) hKk0) Real.pi_pos.le
    linarith only [abs_nonneg b.re, abs_nonneg b.im, hΞ0, h1]
  have hRdμ : Rd ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hRμ : R ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hR₀μ : R₀ ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hΞμ : Ξ ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hcμ : c ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hcbμ : cb ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hKkμ : Kk ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hChμ : Ch ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hK₀μ : K₀ ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hK₁μ : K₁ ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hμ100 : 100 ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  have hR₀1μ : R₀ + 1 ≤ μ := by
    linarith only [hμsum, hRd.le, hRpos.le, hR₀pos.le, hΞ0, hc0, hcb0, hKk0, hCh0, hK₀0, hK₁0]
  -- ## the choice of `X₁`
  have hμX₁ : μ ≤ X₁ := by
    rw [hX₁]
    have h4 : μ ^ 1 ≤ μ ^ 4 := pow_le_pow_right₀ hμ1 (by norm_num)
    have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 8 := by norm_num
    have h5 : μ ^ 4 ≤ (10 : ℝ) ^ 8 * μ ^ 4 := by nlinarith only [hone, pow_pos hμpos 4]
    exact le_trans (by simpa using h4) h5
  have hX₁1 : 1 ≤ X₁ := le_trans hμ1 hμX₁
  have hX₁pos : 0 < X₁ := lt_of_lt_of_le zero_lt_one hX₁1
  have h64μX₁ : 64 * μ ^ 2 ≤ X₁ := by
    rw [hX₁]
    have h24 : μ ^ 2 ≤ μ ^ 4 := pow_le_pow_right₀ hμ1 (by norm_num)
    have h1 : 64 * μ ^ 2 ≤ 64 * μ ^ 4 := by nlinarith only [h24]
    have h2 : (64 : ℝ) ≤ (10 : ℝ) ^ 8 := by norm_num
    have h3 : 64 * μ ^ 4 ≤ (10 : ℝ) ^ 8 * μ ^ 4 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hμpos.le 4)
    linarith only [h1, h3]
  have h100μX₁ : 100 * μ ≤ X₁ := by
    rw [hX₁]
    have h3 : μ ≤ μ ^ 4 := by
      simpa using pow_le_pow_right₀ hμ1 (show 1 ≤ 4 by norm_num)
    have h1 : 100 * μ ≤ 100 * μ ^ 4 := by nlinarith only [h3]
    have h2 : (100 : ℝ) ≤ (10 : ℝ) ^ 8 := by norm_num
    have h4 : 100 * μ ^ 4 ≤ (10 : ℝ) ^ 8 * μ ^ 4 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hμpos.le 4)
    linarith only [h1, h4]
  -- ## the choice of `Ms`
  have hμMs : μ ≤ Ms := by
    rw [hMs]
    have h8 : μ ^ 1 ≤ μ ^ 8 := pow_le_pow_right₀ hμ1 (by norm_num)
    have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    have h5 : μ ^ 8 ≤ (10 : ℝ) ^ 10 * μ ^ 8 := by nlinarith only [hone, pow_pos hμpos 8]
    exact le_trans (by simpa using h8) h5
  have hMspos : 0 < Ms := lt_of_lt_of_le zero_lt_one (le_trans hμ1 hμMs)
  have h64μMs : 64 * μ ^ 2 ≤ Ms := by
    rw [hMs]
    have h28 : μ ^ 2 ≤ μ ^ 8 := pow_le_pow_right₀ hμ1 (by norm_num)
    have h1 : 64 * μ ^ 2 ≤ 64 * μ ^ 8 := by nlinarith only [h28]
    have h2 : (64 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    have h3 : 64 * μ ^ 8 ≤ (10 : ℝ) ^ 10 * μ ^ 8 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hμpos.le 8)
    linarith only [h1, h3]
  have h24μMs : 24 * μ ≤ Ms := by
    rw [hMs]
    have h18 : μ ≤ μ ^ 8 := by
      simpa using pow_le_pow_right₀ hμ1 (show 1 ≤ 8 by norm_num)
    have h1 : 24 * μ ≤ 24 * μ ^ 8 := by nlinarith only [h18]
    have h2 : (24 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    have h3 : 24 * μ ^ 8 ≤ (10 : ℝ) ^ 10 * μ ^ 8 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hμpos.le 8)
    linarith only [h1, h3]
  have h100μMs : 100 * μ ≤ Ms := by
    rw [hMs]
    have h18 : μ ≤ μ ^ 8 := by
      simpa using pow_le_pow_right₀ hμ1 (show 1 ≤ 8 by norm_num)
    have h1 : 100 * μ ≤ 100 * μ ^ 8 := by nlinarith only [h18]
    have h2 : (100 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    have h3 : 100 * μ ^ 8 ≤ (10 : ℝ) ^ 10 * μ ^ 8 :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg hμpos.le 8)
    linarith only [h1, h3]
  have hX₁Ms : X₁ + 1 ≤ Ms := by
    rw [hX₁, hMs]
    have hμ4 : 1 ≤ μ ^ 4 := one_le_pow₀ hμ1
    have h1 : (1 : ℝ) ≤ (10 : ℝ) ^ 8 * μ ^ 4 := by nlinarith only [hμ4]
    have h3 : (10 : ℝ) ^ 8 ≤ (10 : ℝ) ^ 10 := by norm_num
    have h4 : (10 : ℝ) ^ 8 * μ ^ 4 ≤ (10 : ℝ) ^ 10 * μ ^ 4 :=
      mul_le_mul_of_nonneg_right h3 (pow_nonneg hμpos.le 4)
    have h8 : μ ^ 4 ≤ μ ^ 8 := pow_le_pow_right₀ hμ1 (by norm_num)
    have h5 : (10 : ℝ) ^ 10 * μ ^ 4 ≤ (10 : ℝ) ^ 10 * μ ^ 8 :=
      mul_le_mul_of_nonneg_left h8 (by positivity)
    linarith only [h1, h4, h5]
  -- ## derived bounds
  have h64cX₁ : 64 * c ^ 2 ≤ X₁ := by
    have h : c ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hc0 hcμ 2
    linarith only [h64μX₁, h]
  have h64KkX₁ : 64 * Kk ^ 2 ≤ X₁ := by
    have h : Kk ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hKk0 hKkμ 2
    linarith only [h64μX₁, h]
  have h64KkX₁' : 64 * (|a.re| + |a.im|) ^ 2 ≤ X₁ := by
    have h : (|a.re| + |a.im|) ^ 2 = Kk ^ 2 := by rw [hKk]
    rw [h]; exact h64KkX₁
  have hRdX₁ : Rd ≤ X₁ := le_trans hRdμ hμX₁
  have hξX₁ : d.ξ₀ + 1 < X₁ := lt_of_lt_of_le hRξ (le_trans hRμ hμX₁)
  have hRexpX₁ : Real.exp Real.pi ≤ X₁ := le_trans hRexp (le_trans hRμ hμX₁)
  have hKkX₁ : Kk ≤ X₁ := le_trans hKkμ hμX₁
  have hKkX₁' : |a.re| + |a.im| ≤ X₁ := by rw [← hKk]; exact hKkX₁
  have hR₀X₁ : R₀ + 1 ≤ X₁ := by linarith only [hR₀1μ, hμX₁]
  have hBn0 : 0 ≤ Bn := by
    rw [hBn]
    have hlog0 : 0 ≤ Real.log (X₁ + 1) := Real.log_nonneg (by linarith only [hX₁1])
    have h1 : 0 ≤ c * Real.log (X₁ + 1) := mul_nonneg hc0 hlog0
    linarith only [h1, hcb0]
  refine ⟨X₁, Ms, Bn, hX₁pos, hMspos, hRdX₁, hX₁Ms, hξX₁, hBn0, ?_⟩
  intro α hInF1 hQAdm M hMsM hαM hmem
  -- ## bounds for `M`
  have hμM : μ ≤ M := le_trans hμMs hMsM
  have hM1 : 1 ≤ M := le_trans hμ1 hμM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hRM : R ≤ M := le_trans hRμ hμM
  have hexpM : Real.exp Real.pi ≤ M := le_trans hRexp hRM
  have hX₁M : X₁ ≤ M := by linarith only [hX₁Ms, hMsM]
  have hR₀M : R₀ + 1 ≤ M := by linarith only [hR₀1μ, hμM]
  have h64cM : 64 * ‖a‖ ^ 2 ≤ M := by
    have h : c ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hc0 hcμ 2
    have h1 : 64 * c ^ 2 ≤ Ms := by linarith only [h64μMs, h]
    rw [← hc]; exact le_trans h1 hMsM
  have h12cbM : 12 * (‖b‖ + 1) ≤ M := by
    have h1 : cb + 1 ≤ 2 * μ := by linarith only [hcbμ, hμ1]
    have h2 : 12 * (cb + 1) ≤ 24 * μ := by linarith only [h1]
    rw [← hcb]
    linarith only [h2, h24μMs, hMsM]
  have hcharith : 2 * (Rd + Ch + 1) ≤ M := by
    have h1 : Rd + Ch + 1 ≤ 3 * μ := by linarith only [hRdμ, hChμ, hμ1]
    have h2 : 2 * (Rd + Ch + 1) ≤ 6 * μ := by linarith only [h1]
    have h3 : 6 * μ ≤ 100 * μ := by linarith only [hμpos]
    linarith only [h2, h3, h100μMs, hMsM]
  -- ## facts about `α`
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hαne : α ≠ 0 := by
    intro h; rw [h] at hαre; simpa using hαre
  have hnsq : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hAre : 0 ≤ (1 / α).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg hαre.le hnsq.le
  have hnorm1 : 2 * M ≤ ‖1 / α‖ := by
    have h : ‖1 / α‖ = 1 / ‖α‖ := by rw [norm_div, norm_one]
    rw [h, le_div_iff₀ (norm_pos_iff.mpr hαne)]
    linarith only [hαM]
  have hAB : (1 / α).re + |(1 / α).im| ≥ ‖1 / α‖ := by
    have hsq : ‖1 / α‖ ^ 2 = (1 / α).re ^ 2 + (1 / α).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h1 : (1 / α).im ^ 2 = |(1 / α).im| ^ 2 := by rw [sq_abs]
    have h2 : ((1 / α).re + |(1 / α).im|) ^ 2 ≥ ‖1 / α‖ ^ 2 := by
      rw [hsq, h1]; nlinarith only [hAre, abs_nonneg ((1 / α).im)]
    have h3 : 0 ≤ (1 / α).re + |(1 / α).im| := by positivity
    nlinarith only [h2, h3, norm_nonneg (1 / α)]
  have h2M : 2 * M ≤ (1 / α).re + |(1 / α).im| := le_trans hnorm1 hAB
  -- ## the anchor margin
  have h64KkM : 64 * Kk ^ 2 ≤ M := by
    have h : Kk ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hKk0 hKkμ 2
    linarith only [h64μMs, h, hMsM]
  have hlogKkM : Kk * Real.log M ≤ M / 4 := mul_log_le_div hKk0 hM1 h64KkM
  have hanch : Rd + 1 / 2 ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) := by
    have hA : M - (2 * (|a.re| + |a.im|) * Real.log M
          + (2 * (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 4))
        ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) :=
      wc_margA_anchor_ge (M := M) d hasym hRM hexpM hInF1 hαM
    have hCh' : Ch = 2 * (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 4 := by
      rw [hCh, hKk]
    have hKk' : Kk = |a.re| + |a.im| := hKk
    have hA' : M - (2 * Kk * Real.log M + Ch) ≤
        Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) := by
      rw [hCh', hKk']; exact hA
    have h2 : M / 2 - Ch ≤ M - (2 * Kk * Real.log M + Ch) := by
      linarith only [hlogKkM]
    have h3 : Rd + 1 / 2 ≤ M / 2 - Ch := by linarith only [hcharith]
    linarith only [hA', h2, h3]
  -- ## the walk
  have hmemM : Work.Pert.Xc d (-(M : ℂ)) ∈ Work.Pert.Qm Ξ α := by simpa using hmem
  obtain ⟨nA, hnA_lo, hnA_hi, hmemA, hstepA, hdefA, _, _, _, _, _, _⟩ :=
    hwalkmain hQAdm hR₀M hmemM
  set n : ℕ := ⌊M - X₁⌋₊ with hn
  have hn_le : (n : ℝ) ≤ M - X₁ := by
    have h0 : (0 : ℝ) ≤ M - X₁ := by linarith only [hX₁M]
    simpa [hn] using Nat.floor_le h0
  have hn_lt : M - X₁ < (n : ℝ) + 1 := by
    simpa [hn] using Nat.lt_floor_add_one (M - X₁)
  have hMn_ge : X₁ ≤ M - (n : ℝ) := by linarith only [hn_le]
  have hMn_le : M - (n : ℝ) ≤ X₁ + 1 := by linarith only [hn_lt]
  have hn_le_nA : n ≤ nA := by
    have h1 : (n : ℝ) ≤ (nA : ℝ) := by linarith only [hMn_ge, hnA_hi, hR₀X₁]
    exact_mod_cast h1
  have hx₀1 : 1 ≤ M - (n : ℝ) := le_trans hX₁1 hMn_ge
  have hx₀R : R ≤ M - (n : ℝ) := le_trans (le_trans hRμ hμX₁) hMn_ge
  have hlog : Real.log (M - (n : ℝ)) ≤ Real.log (X₁ + 1) :=
    Real.log_le_log (by linarith only [hMn_ge, hX₁1]) hMn_le
  have hKklog : (|a.re| + |a.im|) * Real.log (X₁ + 1) ≤ X₁ / 4 + (|a.re| + |a.im|) := by
    have h1 : Real.log (X₁ + 1) ≤ 1 + Real.log X₁ := log_succ_le_one_add_log hX₁1
    have h2 : (|a.re| + |a.im|) * Real.log X₁ ≤ X₁ / 4 :=
      mul_log_le_div hKk0' hX₁1 h64KkX₁'
    nlinarith only [h1, h2, hKk0']
  have hKklog' : (|a.re| + |a.im|) * Real.log (M - (n : ℝ)) ≤
      X₁ / 4 + (|a.re| + |a.im|) := by
    have h := mul_le_mul_of_nonneg_left hlog hKk0'
    linarith only [hKklog, h]
  have hsmall : (|a.re| + |a.im|) * Real.pi + |b.re| + 1 ≤ 4 * μ := by
    have hπ : 0 ≤ (|a.re| + |a.im|) * Real.pi := mul_nonneg hKk0' Real.pi_pos.le
    have hrest : 0 ≤ |b.re| + |b.im| + Ξ + 4 := by
      linarith only [abs_nonneg b.re, abs_nonneg b.im, hΞ0]
    have h1 : (|a.re| + |a.im|) * Real.pi ≤ Ch := by
      rw [hCh, hKk]; linarith only [hπ, hrest]
    linarith only [h1, hChμ, hcbμ, hμ1, hbre]
  have hbnd : ‖a‖ * Real.log (M - (n : ℝ)) + ‖b‖ + 1 ≤ Bn := by
    rw [hBn, hc, hcb]
    have h := mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
    linarith only [h]
  refine ⟨n, hMn_ge, hMn_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hmemA j (le_trans hj hn_le_nA)
  · intro j hj
    exact hstepA j (lt_of_lt_of_le hj hn_le_nA)
  · intro j hj
    exact hdefA j (lt_of_lt_of_le hj hn_le_nA)
  · -- `margA ≥ Rd` on the walk
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hxM : M - (j : ℝ) ≤ M := by linarith only [Nat.cast_nonneg (α := ℝ) j]
    have hxX₁ : X₁ ≤ M - (j : ℝ) := by linarith only [hMn_ge, hj']
    have hxR : R ≤ M - (j : ℝ) := le_trans (le_trans hRμ hμX₁) hxX₁
    have hx1 : 1 ≤ M - (j : ℝ) := le_trans hX₁1 hxX₁
    have hxpos : 0 < M - (j : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have h2c : 2 * ‖a‖ ≤ M - (j : ℝ) := by
      rw [← hc]
      linarith only [h100μX₁, hcμ, hμ1, hxX₁]
    have hmb := anchor_walk_margA (Ξ := Ξ) (α := α) (x := M - (j : ℝ)) d hasym hxR hRM hx1 hxM
    have hgap := two_mul_log_div_le (c := ‖a‖) (x := M - (j : ℝ)) (M := M)
      (norm_nonneg a) hxpos h2c hxM
    linarith only [hanch, hmb, hgap]
  · -- `margB ≥ Rd` on the walk
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hxM : M - (j : ℝ) ≤ M := by linarith only [Nat.cast_nonneg (α := ℝ) j]
    have hxX₁ : X₁ ≤ M - (j : ℝ) := by linarith only [hMn_ge, hj']
    have hxR : R ≤ M - (j : ℝ) := le_trans (le_trans hRμ hμX₁) hxX₁
    have hlin : Rd + (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 1 ≤ 3 * X₁ / 4 := by
      have hπ : 0 ≤ (|a.re| + |a.im|) * Real.pi := mul_nonneg hKk0' Real.pi_pos.le
      have hrest : 0 ≤ |b.re| + |b.im| + Ξ + 4 := by
        linarith only [abs_nonneg b.re, abs_nonneg b.im, hΞ0]
      have h1 : (|a.re| + |a.im|) * Real.pi ≤ Ch := by
        rw [hCh, hKk]; linarith only [hπ, hrest]
      linarith only [h1, hChμ, hcbμ, hμ1, hbre, hbim, hRdμ, hΞμ, h100μX₁]
    exact wc_margB_axis_ge (α := α) (x := M - (j : ℝ)) (X₁ := X₁) (Rd := Rd)
      d hasym hxR hxX₁ hX₁1 hRexpX₁ hKkX₁' h64KkX₁' hlin
  · -- `‖α‖ ‖Xc‖ ≤ 2/3` on the walk
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hxM : M - (j : ℝ) ≤ M := by linarith only [Nat.cast_nonneg (α := ℝ) j]
    have hxX₁ : X₁ ≤ M - (j : ℝ) := by linarith only [hMn_ge, hj']
    have hxR : R ≤ M - (j : ℝ) := le_trans (le_trans hRμ hμX₁) hxX₁
    have hx1 : 1 ≤ M - (j : ℝ) := le_trans hX₁1 hxX₁
    have haX : ‖a‖ ≤ M - (j : ℝ) := by
      rw [← hc]; linarith only [hcμ, hμX₁, hxX₁]
    have h64x : 64 * ‖a‖ ^ 2 ≤ M - (j : ℝ) := by
      rw [← hc]; linarith only [h64cX₁, hxX₁]
    have hbx : ‖b‖ + 65 ≤ 3 * (M - (j : ℝ)) / 4 := by
      rw [← hcb]
      have h1 : cb + 65 ≤ 2 * μ := by linarith only [hcbμ, hμ100]
      have h2 : 2 * μ ≤ 3 * X₁ / 4 := by linarith only [h100μX₁, hμ1]
      have h3 : 3 * X₁ / 4 ≤ 3 * (M - (j : ℝ)) / 4 := by linarith only [hxX₁]
      linarith only [h1, h2, h3]
    exact (wc_Xc_axis_norm_pair (α := α) (x := M - (j : ℝ)) d hasym hxR hx1 hxM haX h64x hbx
      hM1 hαM h64cM h12cbM).2
  · -- `64 ≤ ‖Xc‖` on the walk
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hxM : M - (j : ℝ) ≤ M := by linarith only [Nat.cast_nonneg (α := ℝ) j]
    have hxX₁ : X₁ ≤ M - (j : ℝ) := by linarith only [hMn_ge, hj']
    have hxR : R ≤ M - (j : ℝ) := le_trans (le_trans hRμ hμX₁) hxX₁
    have hx1 : 1 ≤ M - (j : ℝ) := le_trans hX₁1 hxX₁
    have haX : ‖a‖ ≤ M - (j : ℝ) := by
      rw [← hc]; linarith only [hcμ, hμX₁, hxX₁]
    have h64x : 64 * ‖a‖ ^ 2 ≤ M - (j : ℝ) := by
      rw [← hc]; linarith only [h64cX₁, hxX₁]
    have hbx : ‖b‖ + 65 ≤ 3 * (M - (j : ℝ)) / 4 := by
      rw [← hcb]
      have h1 : cb + 65 ≤ 2 * μ := by linarith only [hcbμ, hμ100]
      have h2 : 2 * μ ≤ 3 * X₁ / 4 := by linarith only [h100μX₁, hμ1]
      have h3 : 3 * X₁ / 4 ≤ 3 * (M - (j : ℝ)) / 4 := by linarith only [hxX₁]
      linarith only [h1, h2, h3]
    exact (wc_Xc_axis_norm_pair (α := α) (x := M - (j : ℝ)) d hasym hxR hx1 hxM haX h64x hbx
      hM1 hαM h64cM h12cbM).1
  · have hland1 := (wc_Xc_axis_landing (x := M - (n : ℝ)) d hasym hx₀R hx₀1).1
    linarith only [hland1, hbnd]
  · have hland2 := (wc_Xc_axis_landing (x := M - (n : ℝ)) d hasym hx₀R hx₀1).2
    linarith only [hland2, hKklog', hsmall, hMn_ge, h100μX₁, hKkμ, hμ1]
  · have hland2 := (wc_Xc_axis_landing (x := M - (n : ℝ)) d hasym hx₀R hx₀1).2
    linarith only [hland2, hKklog', hsmall, hMn_ge, h100μX₁, hΞμ, hKkμ, hμ1]

end

end Work.Pert.PinLogDev
