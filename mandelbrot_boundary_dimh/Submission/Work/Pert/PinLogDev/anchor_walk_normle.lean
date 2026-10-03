import Mathlib
import Submission.Work.Pert.dev_base_v3

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# `Work.Pert.PinLogDev.anchor_walk_normle`

At an *anchor* point `z` of the pinned walk the `A`-margin `margA Ξ α z` being positive
forces `‖α‖` to be so small that `‖α‖ (M + ‖a‖ log M + ‖b‖ + 1) ≤ 2`, where `M` is the depth
of the anchor (`z` lies within `1/1024` of `-M + a log M + b`) and `10 ^ 6 μ ^ 2 ≤ M`,
`‖a‖, ‖b‖ ≤ μ`, `0 ≤ Ξ ≤ μ`.

The whole content is the observation that the `A`-margin

  `margA Ξ α z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|`

dominates `z.re - Ξ + ‖1/α‖ - |z.im|`, so `margA Ξ α z > 0` gives (with `z.re ≈ -M`)

  `√2 ‖1/α‖ > Ξ - z.re - |z.im| ≥ M - 2 μ log M - 2 μ - 1/512`,

i.e. `‖α‖ ≲ √2 / M`; and `M ≥ 10 ^ 6 μ ^ 2` makes `M + μ log M + μ + 1 ≪ √2 · M / 2` (through
`log M ≤ 2 √M` and `1000 μ ≤ √M`), which closes the constant `2`.
-/

namespace Work.Pert.PinLogDev

open Complex

noncomputable section

/-- The pure arithmetic core: with `μ L ≤ M / 500`, `μ ≤ M / 1000` and `M ≥ 1000` the factor
`M + μ L + μ + 1` is at most `√2⁻¹ · 2 · (M - 2 μ L - 2 μ - 1/512)`. -/
private lemma arith_core {M μ L : ℝ} (hμ0 : 0 ≤ μ) (hL : 0 ≤ L)
    (hμL : μ * L ≤ M / 500) (hμle : μ ≤ M / 1000) (hM1000 : 1000 ≤ M) :
    Real.sqrt 2 * (M + μ * L + μ + 1) ≤ 2 * (M - 2 * (μ * L) - 2 * μ - 1 / 512) := by
  have h1 : (11 / 2) * (μ * L) ≤ (11 / 2) * (M / 500) :=
    mul_le_mul_of_nonneg_left hμL (by norm_num)
  have h2 : (11 / 2) * μ ≤ (11 / 2) * (M / 1000) :=
    mul_le_mul_of_nonneg_left hμle (by norm_num)
  have h3 : (1 : ℝ) ≤ M / 1000 := by linarith
  have h4 : (3 / 2 : ℝ) ≤ (3 / 2) * (M / 1000) := by linarith
  have h5 : (1 / 256 : ℝ) ≤ M / 1000 := by linarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hfac : 0 ≤ M + μ * L + μ + 1 := by
    have : 0 ≤ μ * L := mul_nonneg hμ0 hL
    linarith
  calc Real.sqrt 2 * (M + μ * L + μ + 1)
      ≤ (3 / 2) * (M + μ * L + μ + 1) := mul_le_mul_of_nonneg_right hs2 hfac
    _ ≤ 2 * (M - 2 * (μ * L) - 2 * μ - 1 / 512) := by linarith

/-- If the `A`-margin at `z` is positive then `‖α‖ < √2 / Q` for every positive `Q` below
`Ξ - z.re - |z.im|`.  Indeed `margA Ξ α z > 0` gives
`Ξ - z.re < (1/α).re + |z.im + (1/α).im| ≤ ‖1/α‖ + |z.im|`. -/
private lemma norm_le_of_margA {Ξ Q : ℝ} {α z : ℂ}
    (hm : 0 < Work.Pert.margA Ξ α z) (hQ : Q ≤ Ξ - z.re - |z.im|) (hQ0 : 0 < Q) :
    ‖α‖ < Real.sqrt 2 / Q := by
  have hm' : Ξ - z.re < (1 / α).re + |z.im + (1 / α).im| := by
    have := hm
    simp only [Work.Pert.margA] at this
    linarith
  have h2 : Ξ - z.re - |z.im| < (1 / α).re + |(1 / α).im| := by
    have := abs_add_le z.im ((1 / α).im)
    linarith
  have h3 : Q < (1 / α).re + |(1 / α).im| := lt_of_le_of_lt hQ h2
  -- `(1/α).re + |(1/α).im| ≤ √2 ‖1/α‖`
  have h4 : (1 / α).re + |(1 / α).im| ≤ Real.sqrt 2 * ‖(1 / α : ℂ)‖ := by
    have hsq : ((1 / α).re + |(1 / α).im|) ^ 2
        ≤ 2 * (((1 / α).re) ^ 2 + ((1 / α).im) ^ 2) := by
      nlinarith [sq_nonneg ((1 / α).re - |(1 / α).im|), sq_abs ((1 / α).im)]
    have hnorm2 : ‖(1 / α : ℂ)‖ ^ 2 = ((1 / α).re) ^ 2 + ((1 / α).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hsq' : ((1 / α).re + |(1 / α).im|) ^ 2
        ≤ (Real.sqrt 2 * ‖(1 / α : ℂ)‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm2]
      exact hsq
    have := (sq_le_sq).mp hsq'
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))] at this
    exact le_trans (le_abs_self _) this
  have h5 : Q < Real.sqrt 2 * ‖(1 / α : ℂ)‖ := lt_of_lt_of_le h3 h4
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hζpos : 0 < ‖(1 / α : ℂ)‖ := by nlinarith [h5, hQ0, hs2pos]
  have hαinv : ‖α‖ = 1 / ‖(1 / α : ℂ)‖ := by
    simp [one_div, norm_inv]
  rw [hαinv]
  rw [div_lt_div_iff₀ hζpos hQ0]
  simpa using h5

theorem anchor_walk_normle {Ξ : ℝ} {α z : ℂ} {M μ : ℝ} {a b : ℂ}
    (hμ : 1 ≤ μ) (ha : ‖a‖ ≤ μ) (hb : ‖b‖ ≤ μ) (hΞ : 0 ≤ Ξ) (hΞμ : Ξ ≤ μ)
    (hM : (10 : ℝ) ^ 6 * μ ^ 2 ≤ M)
    (hz : ‖z - (-(M : ℂ) + a * Complex.log (M : ℂ) + b)‖ ≤ 1 / 1024)
    (hm : 0 < Work.Pert.margA Ξ α z) :
    ‖α‖ * (M + ‖a‖ * Real.log M + ‖b‖ + 1) ≤ 2 := by
  -- ## elementary size facts about `M` and `μ`
  have hμ2 : (1 : ℝ) ≤ μ ^ 2 := by nlinarith [hμ]
  have hMbig : (10 : ℝ) ^ 6 ≤ M := by
    have h : (10 : ℝ) ^ 6 * 1 ≤ (10 : ℝ) ^ 6 * μ ^ 2 :=
      mul_le_mul_of_nonneg_left hμ2 (by norm_num)
    linarith
  have hM1000 : (1000 : ℝ) ≤ M := le_trans (by norm_num) hMbig
  have hMpos : 0 < M := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogM_eq : Complex.log (M : ℂ) = (Real.log M : ℂ) :=
    (Complex.ofReal_log (le_of_lt hMpos)).symm
  -- ## the logarithmic bounds `log M ≤ 2 √M`, `1000 μ ≤ √M`
  have hsqrtM_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hL_le : Real.log M ≤ 2 * Real.sqrt M := by
    have h1 : Real.log (Real.sqrt M) ≤ Real.sqrt M - 1 :=
      Real.log_le_sub_one_of_pos hsqrtM_pos
    rw [Real.log_sqrt (le_of_lt hMpos)] at h1
    linarith
  have hμle_sqrt : μ ≤ Real.sqrt M / 1000 := by
    have h : (1000 * μ) ^ 2 ≤ M := by
      have e : (1000 * μ) ^ 2 = (10 : ℝ) ^ 6 * μ ^ 2 := by ring
      rw [e]; exact hM
    have h0 : (0 : ℝ) ≤ 1000 * μ := by linarith
    have h1 : 1000 * μ ≤ Real.sqrt M := (Real.le_sqrt h0 (le_of_lt hMpos)).mpr h
    linarith
  have hμle : μ ≤ M / 1000 := by
    have hsq : Real.sqrt M ≤ M :=
      (Real.sqrt_le_iff).mpr ⟨le_of_lt hMpos, by nlinarith [hM1]⟩
    linarith
  have hμL : μ * Real.log M ≤ M / 500 := by
    have h1 : μ * Real.log M ≤ (Real.sqrt M / 1000) * (2 * Real.sqrt M) :=
      mul_le_mul hμle_sqrt hL_le hlogM_nn (by positivity)
    have h2 : (Real.sqrt M / 1000) * (2 * Real.sqrt M) = M / 500 := by
      have hs : Real.sqrt M ^ 2 = M := Real.sq_sqrt (le_of_lt hMpos)
      calc (Real.sqrt M / 1000) * (2 * Real.sqrt M) = Real.sqrt M ^ 2 / 500 := by ring
        _ = M / 500 := by rw [hs]
    linarith
  -- ## the anchor `z` versus the model point
  let W : ℂ := -(M : ℂ) + a * Complex.log (M : ℂ) + b
  have hzW : ‖z - W‖ ≤ 1 / 1024 := by simpa only [W] using hz
  have hWre : W.re = -M + (a * Complex.log (M : ℂ)).re + b.re := by simp [W]
  have hWim : W.im = (a * Complex.log (M : ℂ)).im + b.im := by simp [W]
  have halog : ‖a * Complex.log (M : ℂ)‖ ≤ μ * Real.log M := by
    rw [hlogM_eq, norm_mul]
    have hnorm : ‖(Real.log M : ℂ)‖ = Real.log M := by
      simp [abs_of_nonneg hlogM_nn]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right ha hlogM_nn
  have hb_re : -b.re ≤ ‖b‖ := le_trans (neg_le_abs b.re) (Complex.abs_re_le_norm b)
  have halog_re : -(a * Complex.log (M : ℂ)).re ≤ ‖a * Complex.log (M : ℂ)‖ :=
    le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
  have hW_re_ge : -M - μ * Real.log M - μ ≤ W.re := by
    rw [hWre]; linarith [halog, hb]
  have hW_re_le : W.re ≤ -M + μ * Real.log M + μ := by
    rw [hWre]
    have h1 : (a * Complex.log (M : ℂ)).re ≤ ‖a * Complex.log (M : ℂ)‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have h2 : b.re ≤ ‖b‖ := le_trans (le_abs_self b.re) (Complex.abs_re_le_norm b)
    linarith [halog, hb]
  -- ## the real and imaginary parts of `z`
  have hz_re_le : z.re ≤ -M + μ * Real.log M + μ + 1 / 1024 := by
    have h : z.re - W.re ≤ 1 / 1024 := by
      have h1 := Complex.re_le_norm (z - W)
      simp only [Complex.sub_re] at h1
      linarith [hzW]
    linarith [hW_re_le, h]
  have hz_re_ge : -M - 1 / 1024 - μ * Real.log M - μ ≤ z.re := by
    have h : W.re - z.re ≤ 1 / 1024 := by
      have h1 := Complex.re_le_norm (W - z)
      simp only [Complex.sub_re] at h1
      have h2 := norm_sub_rev W z
      linarith [hzW, h1, h2]
    linarith [hW_re_ge, h]
  have hW_im_abs : |W.im| ≤ μ * Real.log M + μ := by
    rw [hWim]
    have h1 : |(a * Complex.log (M : ℂ)).im| ≤ ‖a * Complex.log (M : ℂ)‖ :=
      Complex.abs_im_le_norm _
    have h2 : |b.im| ≤ ‖b‖ := Complex.abs_im_le_norm b
    have h3 := abs_add_le ((a * Complex.log (M : ℂ)).im) (b.im)
    linarith [halog, hb]
  have hz_im_abs : |z.im| ≤ μ * Real.log M + μ + 1 / 1024 := by
    have h1 : |z.im - W.im| ≤ ‖z - W‖ := by
      have := Complex.abs_im_le_norm (z - W)
      simpa using this
    have h2 : |z.im| ≤ |W.im| + |z.im - W.im| := by
      have := abs_add_le W.im (z.im - W.im)
      rwa [show W.im + (z.im - W.im) = z.im by ring] at this
    linarith [hW_im_abs, h1, hzW]
  -- ## the margin inequality
  have hX : M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512 ≤ Ξ - z.re - |z.im| := by
    linarith [hΞ, hz_re_le, hz_im_abs]
  have hQpos : 0 < M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512 := by
    have h6 : (1 / 512 : ℝ) ≤ M / 1000 := by linarith
    linarith [hμL, hμle, hM1000, h6]
  have hαlt : ‖α‖ < Real.sqrt 2 / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512) :=
    norm_le_of_margA hm hX hQpos
  -- ## assembling
  have hT : M + ‖a‖ * Real.log M + ‖b‖ + 1 ≤ M + μ * Real.log M + μ + 1 := by
    have h1 : ‖a‖ * Real.log M ≤ μ * Real.log M :=
      mul_le_mul_of_nonneg_right ha hlogM_nn
    linarith [hb]
  have hTpos : 0 < M + ‖a‖ * Real.log M + ‖b‖ + 1 := by
    have h1 : 0 ≤ ‖a‖ * Real.log M := mul_nonneg (norm_nonneg a) hlogM_nn
    have h2 : 0 ≤ ‖b‖ := norm_nonneg b
    linarith
  have hdivpos : 0 < Real.sqrt 2 / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512) :=
    div_pos (Real.sqrt_pos.mpr (by norm_num)) hQpos
  have hmul : ‖α‖ * (M + ‖a‖ * Real.log M + ‖b‖ + 1)
      < (Real.sqrt 2 / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512))
          * (M + μ * Real.log M + μ + 1) :=
    mul_lt_mul hαlt hT hTpos hdivpos.le
  have harith : (Real.sqrt 2 / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512))
      * (M + μ * Real.log M + μ + 1) ≤ 2 := by
    have hmain := arith_core (by linarith : (0 : ℝ) ≤ μ) hlogM_nn hμL hμle hM1000
    have hq := (div_le_iff₀ hQpos).mpr hmain
    calc (Real.sqrt 2 / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512))
          * (M + μ * Real.log M + μ + 1)
        = Real.sqrt 2 * (M + μ * Real.log M + μ + 1)
            / (M - 2 * (μ * Real.log M) - 2 * μ - 1 / 512) := by ring
      _ ≤ 2 := hq
  exact le_of_lt (lt_of_lt_of_le hmul harith)

end

end Work.Pert.PinLogDev
