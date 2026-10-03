import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.PinLogDev.anchor_walk_norm
import Submission.Work.Pert.PinLogDev.anchor_walk_margA
import Submission.Work.Pert.PinLogDev.anchor_walk_normle

set_option maxHeartbeats 4000000

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-! ## Local helper lemmas -/

/-- `margA` shifts by exactly `1` under `z ↦ z + 1`. -/
lemma margA_add_one (Ξ : ℝ) (α z : ℂ) :
    Work.Pert.margA Ξ α (z + 1) = Work.Pert.margA Ξ α z + 1 := by
  unfold Work.Pert.margA
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
  ring

/-- `margB` shifts by exactly `-1` under `z ↦ z + 1`. -/
lemma margB_add_one (Ξ : ℝ) (α z : ℂ) :
    Work.Pert.margB Ξ α (z + 1) = Work.Pert.margB Ξ α z - 1 := by
  unfold Work.Pert.margB
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
  ring

/-- Monotonicity of `t ↦ t - K log t` on `[K, ∞)`. -/
lemma sub_mul_log_mono {K R t : ℝ} (hK : 0 ≤ K) (hRpos : 0 < R) (hKR : K ≤ R)
    (hRt : R ≤ t) : R - K * Real.log R ≤ t - K * Real.log t := by
  have htpos : 0 < t := lt_of_lt_of_le hRpos hRt
  have h1 : Real.log (t / R) ≤ t / R - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log t - Real.log R = Real.log (t / R) := by
    rw [Real.log_div (ne_of_gt htpos) (ne_of_gt hRpos)]
  rw [← h2] at h1
  have h3 : K * (Real.log t - Real.log R) ≤ K * (t / R - 1) :=
    mul_le_mul_of_nonneg_left h1 hK
  have h4 : K * (t / R - 1) = (K / R) * (t - R) := by field_simp
  rw [h4] at h3
  have h5 : K / R ≤ 1 := (div_le_one hRpos).mpr hKR
  have h6 : (K / R) * (t - R) ≤ 1 * (t - R) :=
    mul_le_mul_of_nonneg_right h5 (by linarith)
  nlinarith [h3, h6]

/-- `log R ≤ 2 * sqrt R`. -/
lemma log_le_two_sqrt {R : ℝ} (hR : 0 < R) : Real.log R ≤ 2 * Real.sqrt R := by
  have h1 := Real.log_le_rpow_div (x := R) (ε := (1 / 2 : ℝ)) hR.le (by norm_num)
  have h2 : R ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt R := by
    rw [Real.sqrt_eq_rpow]; ring
  linarith [h1, h2]

/-- `c * log R ≤ R / 4` as soon as `64 c² ≤ R`. -/
lemma mul_log_le_div {c R : ℝ} (hc : 0 ≤ c) (hR : 1 ≤ R) (h : 64 * c ^ 2 ≤ R) :
    c * Real.log R ≤ R / 4 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsl : 8 * c ≤ Real.sqrt R := by
    rw [Real.le_sqrt (x := 8 * c) (y := R) (by positivity) hRpos.le]
    nlinarith [h]
  have h2 : c * (2 * Real.sqrt R) ≤ R / 4 := by
    have hc2 : 2 * c ≤ Real.sqrt R / 4 := by linarith
    have := mul_le_mul_of_nonneg_right hc2 (Real.sqrt_nonneg R)
    have hs : Real.sqrt R * Real.sqrt R = R := by rw [← pow_two]; exact Real.sq_sqrt hRpos.le
    nlinarith [this, hs]
  have h3 : c * Real.log R ≤ c * (2 * Real.sqrt R) :=
    mul_le_mul_of_nonneg_left (log_le_two_sqrt hRpos) hc
  linarith

/-! ## The main theorem -/

theorem anchor_walk {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) :
    ∃ (R₀ K₀ K₁ : ℝ), 0 < R₀ ∧ 0 ≤ K₀ ∧ 0 ≤ K₁ ∧
      ∀ {α : ℂ}, MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
      ∀ {M : ℝ}, R₀ + 1 ≤ M → Work.Pert.Xc d (-(M : ℂ)) ∈ Work.Pert.Qm Ξ α →
      ∃ n : ℕ, R₀ ≤ M - n ∧ M - n ≤ R₀ + 1 ∧
        (∀ j ≤ n, Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)) ∈ Work.Pert.Qm Ξ α) ∧
        (∀ j < n, Work.Pert.F0f f₀ (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)))
            = Work.Pert.Xc d (-(((M - j - 1 : ℝ)) : ℂ))) ∧
        (∀ j < n, ‖Work.Pert.F0f f₀ (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)))
            - (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)) + 1)‖ ≤ 1 / 32) ∧
        (∀ j < n, 30 / 32 ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)) + 1)) ∧
        (∀ j ≤ n, R₀ - (K₀ * Real.log R₀ + K₁) ≤
          Work.Pert.margB Ξ α (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)))) ∧
        (∀ j < n, R₀ - (K₀ * Real.log R₀ + K₁) - 17 / 16 ≤
          Work.Pert.margB Ξ α (Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ)) + 1)) ∧
        (∀ j < n, 64 ≤ ‖Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ))‖) ∧
        (∀ j ≤ n, ‖α‖ * ‖Work.Pert.Xc d (-(((M - j : ℝ)) : ℂ))‖ ≤ 2) ∧
        ‖Work.Pert.Xc d (-(((M - n : ℝ)) : ℂ))‖ ≤ R₀ + K₀ * Real.log R₀ + K₁ + 2 := by
  obtain ⟨a, b, R, hRpos, hRξ, hRexp, hasym⟩ := exists_Xc_axis_asym d
  have hΞ0 : 0 ≤ Ξ := by linarith [hΞ, Real.pi_pos]
  set c : ℝ := ‖a‖ with hc
  set cb : ℝ := ‖b‖ with hcb
  set Kk : ℝ := |a.re| + |a.im| with hKk
  set Cc : ℝ := Kk * Real.pi + |b.re| + |b.im| + Ξ + 1 with hCc
  set Rt : ℝ := max R (max 1 (64 * c)) with hRt
  set μ : ℝ := max 1 (Rt + c + cb + Kk + Cc + Ξ + 1000) with hμ
  set R₀ : ℝ := (10 : ℝ) ^ 8 * μ ^ 4 with hR₀
  set K₀ : ℝ := 2 * c + 2 with hK₀
  set K₁ : ℝ := max (Cc + 1) (c + cb + 2) with hK₁
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg a
  have hcb0 : 0 ≤ cb := by rw [hcb]; exact norm_nonneg b
  have hKk0 : 0 ≤ Kk := by rw [hKk]; positivity
  have hKk2 : Kk ≤ 2 * c := by
    rw [hKk, hc]
    linarith [Complex.abs_re_le_norm a, Complex.abs_im_le_norm a]
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]; nlinarith [hKk0, Real.pi_pos, hΞ0, abs_nonneg b.re, abs_nonneg b.im]
  have hRleRt : R ≤ Rt := by rw [hRt]; exact le_max_left _ _
  have hRt1 : 1 ≤ Rt := by
    rw [hRt]
    exact le_trans (le_max_left 1 (64 * c)) (le_max_right R (max 1 (64 * c)))
  have h64cRt : 64 * c ≤ Rt := by
    rw [hRt]
    exact le_trans (le_max_right 1 (64 * c)) (le_max_right R (max 1 (64 * c)))
  have hRtpos : 0 < Rt := lt_of_lt_of_le hRpos hRleRt
  have hμ1 : 1 ≤ μ := by rw [hμ]; exact le_max_left _ _
  have hsumμ : Rt + c + cb + Kk + Cc + Ξ + 1000 ≤ μ := by
    rw [hμ]; exact le_max_right _ _
  have hcμ : c ≤ μ := le_trans (by linarith) hsumμ
  have hcbμ : cb ≤ μ := le_trans (by linarith) hsumμ
  have hKkμ : Kk ≤ μ := le_trans (by linarith) hsumμ
  have hCcμ : Cc ≤ μ := le_trans (by linarith) hsumμ
  have hΞμ : Ξ ≤ μ := le_trans (by linarith) hsumμ
  have hRtμ : Rt ≤ μ := le_trans (by linarith) hsumμ
  have hμpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ1
  have hR0ge : μ ≤ R₀ := by
    rw [hR₀]
    have h4 : μ ^ 1 ≤ μ ^ 4 := pow_le_pow_right₀ hμ1 (by norm_num)
    have hone : (1 : ℝ) ≤ (10 : ℝ) ^ 8 := by norm_num
    have h5 : μ ^ 4 ≤ (10 : ℝ) ^ 8 * μ ^ 4 := by nlinarith [hone, pow_pos hμpos 4]
    simpa using le_trans h4 h5
  have hR0_1 : 1 ≤ R₀ := le_trans hμ1 hR0ge
  have hR0pos : 0 < R₀ := lt_of_lt_of_le zero_lt_one hR0_1
  have hR0log : 0 ≤ Real.log R₀ := Real.log_nonneg hR0_1
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; linarith [hc0]
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have h : 0 ≤ Cc + 1 := by linarith [hCc0]
    exact le_trans h (le_max_left _ _)
  have hKkK0 : Kk ≤ K₀ := by rw [hK₀]; linarith [hKk2]
  have hCcK1 : Cc ≤ K₁ := by
    rw [hK₁]
    exact le_trans (by linarith [hCc0] : Cc ≤ Cc + 1) (le_max_left _ _)
  have hcbK1 : c + cb ≤ K₁ := by rw [hK₁]; linarith [le_max_right (Cc + 1) (c + cb + 2)]
  have hK0sq : 64 * K₀ ^ 2 ≤ R₀ := by
    have hle : 2 * c + 2 ≤ 4 * μ := by linarith
    have hnn : 0 ≤ 2 * c + 2 := by linarith
    have hsq : (2 * c + 2) ^ 2 ≤ (4 * μ) ^ 2 := pow_le_pow_left₀ hnn hle 2
    have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ1
    rw [hR₀, hK₀]
    nlinarith [hsq, hμ2, sq_nonneg μ, hμ1]
  have hK0log : K₀ * Real.log R₀ ≤ R₀ / 4 := mul_log_le_div hK₀0 hR0_1 hK0sq
  have hK1quarter : K₁ ≤ R₀ / 4 := by
    have h1 : Cc + 1 ≤ 2 * μ := by linarith
    have h2 : c + cb + 2 ≤ 3 * μ := by linarith
    have h3 : K₁ ≤ 3 * μ := by rw [hK₁]; exact max_le (by linarith) h2
    have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ1
    have h4 : 12 * μ ≤ R₀ := by rw [hR₀]; nlinarith [hμ2, sq_nonneg μ, hμ1]
    linarith
  have hRmargin : 0 < R₀ - (K₀ * Real.log R₀ + K₁) := by linarith
  have hRξR0 : d.ξ₀ + 1 < R₀ :=
    lt_of_lt_of_le hRξ (le_trans hRleRt (le_trans hRtμ hR0ge))
  have hhasym : ∀ x : ℝ, Rt ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024 :=
    fun x hx => hasym x (le_trans hRleRt hx)
  refine ⟨R₀, K₀, K₁, hR0pos, hK₀0, hK₁0, ?_⟩
  intro α hQAdm M hM hmem
  have hM1 : 1 ≤ M := by linarith [hR0pos]
  have hR0M : R₀ ≤ M := by linarith
  have hRtM : Rt ≤ M := le_trans hRtμ (le_trans hR0ge hR0M)
  have hRleM : R ≤ M := le_trans hRleRt hRtM
  have hhasymM : ‖Work.Pert.Xc d (-(M : ℂ)) - (-(M : ℂ) + a * Complex.log (M : ℂ) + b)‖
      ≤ 1 / 1024 := hasym M hRleM
  have hmemM : 0 < Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) ∧
      0 < Work.Pert.margB Ξ α (Work.Pert.Xc d (-(M : ℂ))) :=
    (Work.Pert.mem_Qm_iff_marg Ξ α (Work.Pert.Xc d (-(M : ℂ)))).mp hmem
  -- ## the five general facts
  have hB : ∀ x : ℝ, R₀ ≤ x →
      R₀ - (K₀ * Real.log R₀ + K₁) ≤
        Work.Pert.margB Ξ α (Work.Pert.Xc d (-(x : ℂ))) := by
    intro x hx
    have hxRt : Rt ≤ x := le_trans hRtμ (le_trans hR0ge hx)
    have hxR : R ≤ x := le_trans hRleRt hxRt
    have hxexp : Real.exp Real.pi ≤ x := le_trans hRexp (le_trans (le_max_left _ _) hxRt)
    have h1 : x - Kk * Real.log x - Cc ≤ Work.Pert.margB Ξ α (Work.Pert.Xc d (-(x : ℂ))) :=
      margB_Xc_axis_ge d hhasym hxRt hxexp
    have h2 : R₀ - Kk * Real.log R₀ - Cc ≤ x - Kk * Real.log x - Cc := by
      have := sub_mul_log_mono hKk0 hR0pos (le_trans hKkμ hR0ge) hx
      linarith
    have h3 : R₀ - (K₀ * Real.log R₀ + K₁) ≤ R₀ - Kk * Real.log R₀ - Cc := by
      have hK : Kk ≤ K₀ := hKkK0
      have hC : Cc ≤ K₁ := hCcK1
      nlinarith [mul_le_mul_of_nonneg_right hK hR0log]
    linarith
  have hA : ∀ x : ℝ, R₀ ≤ x → x ≤ M - 1 →
      0 < Work.Pert.margA Ξ α (Work.Pert.Xc d (-(x : ℂ))) := by
    intro x hx hxM1
    have hxRt : Rt ≤ x := le_trans hRtμ (le_trans hR0ge hx)
    have hxR : R ≤ x := le_trans hRleRt hxRt
    have hx1 : 1 ≤ x := le_trans hR0_1 hx
    have hchild : Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) + (M - x)
        - 2 * ‖a‖ * Real.log (M / x) - 4 / 1024
        ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(x : ℂ))) :=
      anchor_walk_margA d hasym hxR hRleM hx1 (by linarith)
    have hgap : (1 : ℝ) / 2 ≤ (M - x) - 2 * c * Real.log (M / x) := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hlog : Real.log (M / x) ≤ (M - x) / x := by
        have h1 : Real.log (M / x) ≤ M / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
        have h2 : M / x - 1 = (M - x) / x := by field_simp
        linarith [h1, h2.symm.le, h2.le]
      have hcx : 2 * c / x ≤ 1 / 2 := by
        rw [div_le_iff₀ hxpos]
        have : 4 * c ≤ x := le_trans (le_trans (by linarith [hcμ, hR0ge]) hx) (le_refl x)
        linarith
      have h2 : 2 * c * ((M - x) / x) ≤ (M - x) / 2 := by
        have hh : (2 * c / x) * (M - x) ≤ (1 / 2) * (M - x) :=
          mul_le_mul_of_nonneg_right hcx (by linarith)
        calc 2 * c * ((M - x) / x) = (2 * c / x) * (M - x) := by ring
          _ ≤ (1 / 2) * (M - x) := hh
          _ = (M - x) / 2 := by ring
      have h3 : 2 * c * Real.log (M / x) ≤ 2 * c * ((M - x) / x) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      have h4 : 1 ≤ M - x := by linarith
      linarith
    have h5 := hmemM.1
    linarith
  have hNup : ∀ x : ℝ, R₀ ≤ x → x ≤ M →
      ‖Work.Pert.Xc d (-(x : ℂ))‖ ≤ x + c * Real.log x + cb + 1 := by
    intro x hx hxM
    have hxRt : Rt ≤ x := le_trans hRtμ (le_trans hR0ge hx)
    have hxR : R ≤ x := le_trans hRleRt hxRt
    have hx1 : 1 ≤ x := le_trans hR0_1 hx
    have h := (anchor_walk_norm d hhasym hxRt hx1).1
    simpa [hc, hcb] using h
  have hNlow : ∀ x : ℝ, R₀ ≤ x → 64 ≤ ‖Work.Pert.Xc d (-(x : ℂ))‖ := by
    intro x hx
    have hxRt : Rt ≤ x := le_trans hRtμ (le_trans hR0ge hx)
    have hxR : R ≤ x := le_trans hRleRt hxRt
    have hx1 : 1 ≤ x := le_trans hR0_1 hx
    have h := (anchor_walk_norm d hhasym hxRt hx1).2
    have h64c : 64 * c ^ 2 ≤ R₀ := by
      rw [hR₀]; nlinarith [hcμ, hμ1, sq_nonneg μ, hc0]
    have hml := mul_log_le_div hc0 hR0_1 h64c
    have hmono := sub_mul_log_mono hc0 hR0pos (le_trans hcμ hR0ge) hx
    have hcb4 : cb + 1 ≤ R₀ / 4 := by
      have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ1
      have h8 : 8 * μ ≤ R₀ := by rw [hR₀]; nlinarith [hμ2, sq_nonneg μ, hμ1]
      linarith
    linarith
  have h8 : ∀ x : ℝ, R₀ ≤ x → x ≤ M → ‖α‖ * ‖Work.Pert.Xc d (-(x : ℂ))‖ ≤ 2 := by
    intro x hx hxM
    have hM' : (10 : ℝ) ^ 6 * μ ^ 2 ≤ M := by
      have h6 : (10 : ℝ) ^ 6 * μ ^ 2 ≤ R₀ := by
        rw [hR₀]
        have hμ2 : 1 ≤ μ ^ 2 := one_le_pow₀ hμ1
        nlinarith [hμ2, sq_nonneg μ]
      linarith
    have hC3 := anchor_walk_normle (z := Work.Pert.Xc d (-(M : ℂ))) hμ1 hcμ hcbμ hΞ0 hΞμ hM'
      hhasymM hmemM.1
    have hn := hNup x hx hxM
    have hx1 : 1 ≤ x := le_trans hR0_1 hx
    have hlog : Real.log x ≤ Real.log M := Real.log_le_log (by linarith) hxM
    have hkey : x + c * Real.log x ≤ M + c * Real.log M := by nlinarith [hlog, hc0, hxM]
    have hle : ‖Work.Pert.Xc d (-(x : ℂ))‖ ≤ M + c * Real.log M + cb + 1 := by linarith
    calc ‖α‖ * ‖Work.Pert.Xc d (-(x : ℂ))‖
        ≤ ‖α‖ * (M + c * Real.log M + cb + 1) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg α)
      _ ≤ 2 := by simpa [hc, hcb] using hC3
  -- ## the walk
  set n : ℕ := ⌈M - R₀ - 1⌉₊ with hn
  have hnlow : M - R₀ - 1 ≤ (n : ℝ) := by
    have := Nat.le_ceil (M - R₀ - 1); simpa [hn] using this
  have hnup : (n : ℝ) < M - R₀ := by
    have h0 : (0 : ℝ) ≤ M - R₀ - 1 := by linarith
    have := Nat.ceil_lt_add_one h0
    simpa [hn] using this
  have hMn_low : R₀ ≤ M - (n : ℝ) := by linarith
  have hMn_up : M - (n : ℝ) ≤ R₀ + 1 := by linarith
  refine ⟨n, hMn_low, hMn_up, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have hx2 : M - (j : ℝ) ≤ M := by linarith [(Nat.cast_nonneg (α := ℝ) j)]
    refine (Work.Pert.mem_Qm_iff_marg Ξ α (Work.Pert.Xc d (-((M - (j : ℝ) : ℝ) : ℂ)))).mpr ?_
    refine ⟨?_, ?_⟩
    · by_cases hj0 : j = 0
      · rw [hj0]; simpa using hmemM.1
      · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
          have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
          exact_mod_cast this
        exact hA (M - (j : ℝ)) hx1 (by linarith)
    · exact lt_of_lt_of_le hRmargin (hB (M - (j : ℝ)) hx1)
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have hξ : d.ξ₀ + 1 < M - (j : ℝ) := by linarith [hRξR0]
    exact Xc_F0f_step d hξ
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have hxRt1 : Rt + 1 ≤ M - (j : ℝ) := by
      have : Rt + 1 ≤ μ := by linarith [hRtμ, hμ1]
      linarith [le_trans this hR0ge]
    have hxξ : d.ξ₀ + 1 < M - (j : ℝ) := by linarith [hRξR0]
    have hmax : max Rt 1 + 1 ≤ M - (j : ℝ) := by
      rw [max_eq_left hRt1]; exact hxRt1
    exact F0f_defect_axis_le d hhasym hRtpos hmax hxξ h64cRt
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have hx2 : M - (j : ℝ) ≤ M := by linarith [(Nat.cast_nonneg (α := ℝ) j)]
    have hmg : 0 < Work.Pert.margA Ξ α (Work.Pert.Xc d (-((M - (j : ℝ) : ℝ) : ℂ))) := by
      by_cases hj0 : j = 0
      · rw [hj0]; simpa using hmemM.1
      · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
          have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
          exact_mod_cast this
        exact hA (M - (j : ℝ)) hx1 (by linarith)
    have h1 := margA_add_one Ξ α (Work.Pert.Xc d (-((M - (j : ℝ) : ℝ) : ℂ)))
    rw [h1]; linarith
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    exact hB (M - (j : ℝ)) hx1
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have h5 := hB (M - (j : ℝ)) hx1
    have h2 := margB_add_one Ξ α (Work.Pert.Xc d (-((M - (j : ℝ) : ℝ) : ℂ)))
    rw [h2]; linarith
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    exact hNlow (M - (j : ℝ)) hx1
  · intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have hx1 : R₀ ≤ M - (j : ℝ) := by linarith [hMn_low]
    have hx2 : M - (j : ℝ) ≤ M := by linarith [(Nat.cast_nonneg (α := ℝ) j)]
    exact h8 (M - (j : ℝ)) hx1 hx2
  · have hx1 : R₀ ≤ M - (n : ℝ) := hMn_low
    have hx2 : M - (n : ℝ) ≤ M := by linarith [(Nat.cast_nonneg (α := ℝ) n)]
    have hn1 : 1 ≤ M - (n : ℝ) := le_trans hR0_1 hx1
    have hup := hNup (M - (n : ℝ)) hx1 hx2
    have hlog1 : Real.log (M - (n : ℝ)) ≤ Real.log (R₀ + 1) :=
      Real.log_le_log (by linarith) hMn_up
    have hlog2 : Real.log (R₀ + 1) ≤ 1 + Real.log R₀ := by
      have h2R : R₀ + 1 ≤ 2 * R₀ := by linarith
      have h1 : Real.log (R₀ + 1) ≤ Real.log (2 * R₀) := Real.log_le_log (by linarith) h2R
      have h2 : Real.log (2 * R₀) = Real.log 2 + Real.log R₀ :=
        Real.log_mul (by norm_num) (ne_of_gt hR0pos)
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      linarith
    have hcK0 : c ≤ K₀ := by rw [hK₀]; linarith [hc0]
    have hcbK11 : cb ≤ K₁ := by
      rw [hK₁]; linarith [le_max_right (Cc + 1) (c + cb + 2)]
    linarith [hup, hMn_up, mul_le_mul_of_nonneg_left hlog1 hc0,
      mul_le_mul_of_nonneg_left hlog2 hc0, mul_le_mul_of_nonneg_right hcK0 hR0log, hcbK1]

end

end Work.Pert.PinLogDev
