import Mathlib

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

/-- For `x ≥ 1`, `(log x)^4 ≤ 256 x`.  Proof: `log x = 4 log (x^{1/4}) ≤ 4 x^{1/4}`
(using `Real.log_le_sub_one_of_pos` at `x^{1/4}`), then raise to the fourth power. -/
theorem log_pow_four_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 4 ≤ 256 * x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  set t : ℝ := x ^ ((1:ℝ)/4) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  have hlogt_eq : Real.log t = (1/4 : ℝ) * Real.log x := by rw [htdef, Real.log_rpow hxpos]
  have hlogx : Real.log x ≤ 4 * t := by
    rw [hlogt_eq] at hlogt; linarith
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have h4 : Real.log x ^ 4 ≤ (4 * t)^4 := pow_le_pow_left₀ hlogx_nonneg hlogx 4
  have ht4 : t^4 = x := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
    norm_num
  have hthis : (4*t)^4 = 256 * x := by rw [mul_pow, ht4]; norm_num
  linarith [h4, hthis]

/-- For `Δ ≥ 1`, `⌊logb 2 (4Δ)⌋₊ + 1 ≤ log (8Δ) / log 2`.  Indeed `⌊y⌋₊ ≤ y`, so the left
side is at most `logb 2 (4Δ) + 1 = (log (4Δ) + log 2)/log 2 = log (8Δ)/log 2`. -/
theorem floor_logb_add_one_le (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ≤ Real.log (8 * Δ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (1:ℝ) ≤ 4 * Δ := by linarith
  have hfloor : ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ)) ≤ Real.logb 2 (4 * Δ) :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) h4)
  have hsplit : Real.log (8 * Δ) = Real.log (4 * Δ) + Real.log 2 := by
    have h : (8:ℝ) * Δ = (4 * Δ) * 2 := by ring
    rw [h, Real.log_mul (by linarith) (by norm_num)]
  have hlogb : Real.logb 2 (4 * Δ) + 1 = Real.log (8 * Δ) / Real.log 2 := by
    rw [hsplit]; unfold Real.logb; field_simp
  linarith

theorem CountXYD3_final_arith :
    ∀ K0 : ℝ, 0 < K0 → ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      K0 * Δ ^ 3 * Real.log (8 * Δ) ^ 2 * ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ^ 2 ≤ K * Δ ^ 4 := by
  intro K0 hK0
  refine ⟨2048 * K0 / (Real.log 2)^2, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro Δ hΔ
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
    -- `(log (8Δ))^4 ≤ 2048 Δ`
    have hL4 : Real.log (8 * Δ) ^ 4 ≤ 256 * (8 * Δ) := log_pow_four_le (8 * Δ) (by linarith)
    have hLpow : Real.log (8 * Δ) ^ 4 ≤ 2048 * Δ := by nlinarith [hL4]
    have hLpow' : Real.log (8*Δ)^2 * Real.log (8*Δ)^2 ≤ 2048 * Δ := by
      have h : Real.log (8*Δ)^2 * Real.log (8*Δ)^2 = Real.log (8*Δ)^4 := by ring
      linarith [hLpow, h]
    -- floor bound
    have hGle : ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ≤ Real.log (8 * Δ) / Real.log 2 :=
      floor_logb_add_one_le Δ hΔ
    -- `G * log 2 ≤ log (8Δ)`
    have hGmul : (((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1)) * Real.log 2 ≤ Real.log (8 * Δ) := by
      have h := mul_le_mul_of_nonneg_right hGle (le_of_lt hlog2)
      rwa [div_mul_cancel₀ (Real.log (8*Δ)) hlog2ne] at h
    have hGnonneg : (0:ℝ) ≤ ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) := by positivity
    have hGmul_nn : 0 ≤ ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) * Real.log 2 :=
      mul_nonneg hGnonneg (le_of_lt hlog2)
    have hGsq : ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ^ 2 * (Real.log 2)^2 ≤ Real.log (8*Δ)^2 := by
      have h : (((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) * Real.log 2)^2 ≤ Real.log (8*Δ)^2 :=
        pow_le_pow_left₀ hGmul_nn hGmul 2
      have he : (((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) * Real.log 2)^2
          = ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1)^2 * (Real.log 2)^2 := by ring
      linarith [h, he]
    -- assemble: clear the denominator `(log 2)^2`
    have h1 : K0 * Δ^3 * Real.log (8*Δ)^2
        * (((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ^ 2 * (Real.log 2)^2)
        ≤ K0 * Δ^3 * Real.log (8*Δ)^2 * Real.log (8*Δ)^2 :=
      mul_le_mul_of_nonneg_left hGsq (by positivity)
    have h2 : K0 * Δ^3 * (Real.log (8*Δ)^2 * Real.log (8*Δ)^2) ≤ K0 * Δ^3 * (2048*Δ) :=
      mul_le_mul_of_nonneg_left hLpow' (by positivity)
    have h3 : K0 * Δ^3 * (2048*Δ) = 2048*K0*Δ^4 := by ring
    rw [show 2048 * K0 / (Real.log 2)^2 * Δ^4 = 2048*K0*Δ^4/(Real.log 2)^2 by ring]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (Real.log 2)^2)]
    linarith [h1, h2, h3]

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
