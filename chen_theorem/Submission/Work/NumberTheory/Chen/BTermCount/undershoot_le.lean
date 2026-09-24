import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- The `β`-undershoot at the lower end. For `x ≥ (10/δ)^14` and any `M ≥ x^{1/14}`, the quantity `log(M−1)/log(x+2) = β_{M−1}` is at least `1/14 − δ` (the point is that `log(M−1) ≥ log(x^{1/14} − 1) = (1/14)log x − 2x^{−1/14} + …` while `log(x+2) ≈ log x`). -/
theorem undershoot_le (x M : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1/700)
    (hx : (10/δ)^14 ≤ (x : ℝ)) (hM : (x : ℝ) ^ ((1:ℝ)/14) ≤ (M : ℝ)) :
    (1:ℝ)/14 - δ ≤ Real.log ((M : ℝ) - 1) / Real.log ((x : ℝ) + 2) := by
  -- δ is a small positive number and `10/δ ≥ 7000`
  have h700 : (7000:ℝ) ≤ 10/δ := by
    have h : (1:ℝ) / (1/700) ≤ 1/δ := one_div_le_one_div_of_le hδ hδle
    have h1 : (700:ℝ) ≤ 1/δ := by
      have h' : (1:ℝ)/(1/700) = 700 := by norm_num
      linarith
    rw [div_eq_mul_one_div]
    linarith
  have hdpos : 0 < (10:ℝ)/δ := div_pos (by norm_num) hδ
  -- `x` is huge and positive
  have hX7000 : (7000:ℝ)^14 ≤ (x:ℝ) := by
    have h : (7000:ℝ)^14 ≤ (10/δ)^14 := pow_le_pow_left₀ (by norm_num) h700 14
    linarith
  have hX1 : (1:ℝ) ≤ (x:ℝ) := by
    have h : (1:ℝ) ≤ (7000:ℝ)^14 := by norm_num
    linarith
  have hXpos : 0 < (x:ℝ) := by linarith
  -- `x^{1/14} ≥ 10/δ ≥ 7000`
  have hT10 : (10:ℝ)/δ ≤ (x:ℝ)^((1:ℝ)/14) := by
    have hbase : ((10/δ)^14 : ℝ) ^ ((1:ℝ)/14) = 10/δ := by
      rw [← Real.rpow_natCast (10/δ) 14, ← Real.rpow_mul (le_of_lt hdpos),
        show (((14:ℕ):ℝ) * (1/14)) = 1 by norm_num, Real.rpow_one]
    have h := Real.rpow_le_rpow (x := (10/δ)^14) (y := (x:ℝ))
      (le_of_lt (pow_pos hdpos 14)) hx (by norm_num : (0:ℝ) ≤ 1/14)
    rwa [hbase] at h
  have hT1 : (1:ℝ) < (x:ℝ)^((1:ℝ)/14) := by linarith
  have hTpos : 0 < (x:ℝ)^((1:ℝ)/14) := by linarith
  have hTm1pos : 0 < (x:ℝ)^((1:ℝ)/14) - 1 := by linarith
  have hTm1ne : (x:ℝ)^((1:ℝ)/14) - 1 ≠ 0 := ne_of_gt hTm1pos
  have hTne : (x:ℝ)^((1:ℝ)/14) ≠ 0 := ne_of_gt hTpos
  -- `log (M-1) ≥ log (x^{1/14} - 1)`
  have hMge : (x:ℝ)^((1:ℝ)/14) - 1 ≤ (M:ℝ) - 1 := by linarith
  have hlogM : Real.log ((x:ℝ)^((1:ℝ)/14) - 1) ≤ Real.log ((M:ℝ) - 1) :=
    Real.log_le_log hTm1pos hMge
  have hlogT : Real.log ((x:ℝ)^((1:ℝ)/14)) = (1/14)*Real.log (x:ℝ) := Real.log_rpow hXpos _
  -- `log (x^{1/14} - 1) ≥ (1/14) log x - 1/(x^{1/14} - 1)`
  have hstep : (1/14)*Real.log (x:ℝ) - 1/((x:ℝ)^((1:ℝ)/14) - 1)
      ≤ Real.log ((x:ℝ)^((1:ℝ)/14) - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hTpos hTm1pos)
    rw [Real.log_div hTne hTm1ne] at h
    have hsub : (x:ℝ)^((1:ℝ)/14) / ((x:ℝ)^((1:ℝ)/14) - 1) - 1
        = 1/((x:ℝ)^((1:ℝ)/14) - 1) := by
      field_simp; try ring
    linarith
  -- `log (x+2) ≤ log x + 2/x`
  have hlogX2 : Real.log ((x:ℝ)+2) ≤ Real.log (x:ℝ) + 2/(x:ℝ) := by
    have hXne : (x:ℝ) ≠ 0 := ne_of_gt hXpos
    have harg : 0 < 1 + 2/(x:ℝ) := add_pos one_pos (div_pos (by norm_num) hXpos)
    have hfac : (x:ℝ) + 2 = (x:ℝ) * (1 + 2/(x:ℝ)) := by
      field_simp; try ring
    rw [hfac, Real.log_mul hXne (ne_of_gt harg)]
    have h := Real.log_le_sub_one_of_pos harg
    linarith
  -- numeric lower bounds on the two logarithms
  have hlogD : (1:ℝ)/2 ≤ Real.log (10/δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hdpos
    have h' : ((10:ℝ)/δ)⁻¹ = δ/10 := by field_simp; try ring
    rw [h'] at h
    have hδ10 : δ/10 ≤ 1/7000 := by linarith
    linarith
  have hlogXge : 14 * Real.log (10/δ) ≤ Real.log (x:ℝ) := by
    have h := Real.log_le_log (pow_pos hdpos 14) hx
    rwa [Real.log_pow] at h
  -- the two small error terms
  have hA : 1/((x:ℝ)^((1:ℝ)/14) - 1) ≤ δ/9 := by
    have hpos : 0 < (10:ℝ)/δ - 1 := by linarith
    have hge : (10:ℝ)/δ - 1 ≤ (x:ℝ)^((1:ℝ)/14) - 1 := by linarith
    have h1 := one_div_le_one_div_of_le hpos hge
    have heq : 1/((10:ℝ)/δ - 1) = δ/(10-δ) := by field_simp; try ring
    have h2 : δ/(10-δ) ≤ δ/9 := div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
    linarith
  have hXge10 : (10:ℝ)/δ ≤ (x:ℝ) := by
    have h : (10:ℝ)/δ ≤ ((10:ℝ)/δ)^14 := by
      simpa using pow_le_pow_right₀ (show (1:ℝ) ≤ 10/δ by linarith) (show 1 ≤ 14 by norm_num)
    linarith
  have hδX : (1:ℝ) ≤ δ * (x:ℝ) := by
    have h : δ * ((10:ℝ)/δ) ≤ δ * (x:ℝ) := mul_le_mul_of_nonneg_left hXge10 hδ.le
    have h2 : δ * ((10:ℝ)/δ) = 10 := by field_simp; try ring
    linarith
  have hinv : 1/(x:ℝ) ≤ δ := by
    rw [div_le_iff₀ hXpos]
    linarith
  have hB : ((1:ℝ)/14 - δ) * (2/(x:ℝ)) ≤ δ/7 := by
    have h1 : ((1:ℝ)/14 - δ) * (2/(x:ℝ)) ≤ (1/14) * (2/(x:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (div_pos (by norm_num) hXpos))
    have h2 : (1/14:ℝ) * (2/(x:ℝ)) = 1/(7*(x:ℝ)) := by field_simp; try ring
    have h3 : (1:ℝ)/(7*(x:ℝ)) = (1/7) * (1/(x:ℝ)) := by field_simp; try ring
    have h4 : (1/7) * (1/(x:ℝ)) ≤ (1/7) * δ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    have h5 : (1/7) * δ = δ/7 := by ring
    linarith
  -- the main numerical gain: `δ log x ≥ 7δ` beats both error terms
  have hC : 7*δ ≤ δ * Real.log (x:ℝ) := by
    have h7 : (7:ℝ) ≤ Real.log (x:ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_right h7 hδ.le
    linarith
  have hlogX2pos : 0 < Real.log ((x:ℝ)+2) := Real.log_pos (by linarith)
  rw [le_div_iff₀ hlogX2pos]
  have h2 : ((1:ℝ)/14 - δ) * Real.log ((x:ℝ)+2)
      ≤ ((1:ℝ)/14 - δ) * (Real.log (x:ℝ) + 2/(x:ℝ)) :=
    mul_le_mul_of_nonneg_left hlogX2 (by linarith)
  linarith [h2, hA, hB, hC, hstep, hlogM, hδ.le]

end Work.NumberTheory.Chen.BTermCount
