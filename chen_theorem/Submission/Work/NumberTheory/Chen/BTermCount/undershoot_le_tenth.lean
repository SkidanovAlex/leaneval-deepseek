import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.undershoot_le

namespace Work.NumberTheory.Chen.BTermCount

/-- **The `β`-undershoot at the sift limit `x^{1/10}`.** For `x ≥ (10/δ)^10` and any `M ≥ x^{1/10}`,
the quantity `log (M−1)/log (x+2)` is at least `1/10 − δ`, for `0 < δ ≤ 1/700`.

This is *exactly* the existing `undershoot_le` (`Submission.Work.NumberTheory.Chen.BTermCount.undershoot_le`,
sorry-free) with the exponent `14` replaced by `10` everywhere and `1/14` by `1/10`.
The proof is a mechanical copy of that file with the constants changed (`1/14 ↦ 1/10`, `14 ↦ 10`,
`7000^14 ↦ 7000^10`): `log (x^{1/10} − 1) ≥ (1/10)·log x − 1/(x^{1/10} − 1)` while
`log (x+2) ≤ log x + 2/x`; the errors are `1/(x^{1/10}−1) ≤ δ/9` and `((1/10) − δ)·(2/x) ≤ δ/5` (note `(1/10)·(2/x) = 1/(5x)`,
so `δ/7` would be false here)
and they are dominated by `δ·log x ≥ 5δ` (which follows from `log x ≥ 10·log(10/δ) ≥ 5`; the
constant `14` version used `log x ≥ 14·(1/2) = 7`). -/
theorem undershoot_le_tenth (x M : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1/700)
    (hx : (10/δ)^10 ≤ (x : ℝ)) (hM : (x : ℝ) ^ ((1:ℝ)/10) ≤ (M : ℝ)) :
    (1:ℝ)/10 - δ ≤ Real.log ((M : ℝ) - 1) / Real.log ((x : ℝ) + 2) := by
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
  have hX7000 : (7000:ℝ)^10 ≤ (x:ℝ) := by
    have h : (7000:ℝ)^10 ≤ (10/δ)^10 := pow_le_pow_left₀ (by norm_num) h700 10
    linarith
  have hX1 : (1:ℝ) ≤ (x:ℝ) := by
    have h : (1:ℝ) ≤ (7000:ℝ)^10 := by norm_num
    linarith
  have hXpos : 0 < (x:ℝ) := by linarith
  -- `x^{1/10} ≥ 10/δ ≥ 7000`
  have hT10 : (10:ℝ)/δ ≤ (x:ℝ)^((1:ℝ)/10) := by
    have hbase : ((10/δ)^10 : ℝ) ^ ((1:ℝ)/10) = 10/δ := by
      rw [← Real.rpow_natCast (10/δ) 10, ← Real.rpow_mul (le_of_lt hdpos),
        show (((10:ℕ):ℝ) * (1/10)) = 1 by norm_num, Real.rpow_one]
    have h := Real.rpow_le_rpow (x := (10/δ)^10) (y := (x:ℝ))
      (le_of_lt (pow_pos hdpos 10)) hx (by norm_num : (0:ℝ) ≤ 1/10)
    rwa [hbase] at h
  have hT1 : (1:ℝ) < (x:ℝ)^((1:ℝ)/10) := by linarith
  have hTpos : 0 < (x:ℝ)^((1:ℝ)/10) := by linarith
  have hTm1pos : 0 < (x:ℝ)^((1:ℝ)/10) - 1 := by linarith
  have hTm1ne : (x:ℝ)^((1:ℝ)/10) - 1 ≠ 0 := ne_of_gt hTm1pos
  have hTne : (x:ℝ)^((1:ℝ)/10) ≠ 0 := ne_of_gt hTpos
  -- `log (M-1) ≥ log (x^{1/10} - 1)`
  have hMge : (x:ℝ)^((1:ℝ)/10) - 1 ≤ (M:ℝ) - 1 := by linarith
  have hlogM : Real.log ((x:ℝ)^((1:ℝ)/10) - 1) ≤ Real.log ((M:ℝ) - 1) :=
    Real.log_le_log hTm1pos hMge
  have hlogT : Real.log ((x:ℝ)^((1:ℝ)/10)) = (1/10)*Real.log (x:ℝ) := Real.log_rpow hXpos _
  -- `log (x^{1/10} - 1) ≥ (1/10) log x - 1/(x^{1/10} - 1)`
  have hstep : (1/10)*Real.log (x:ℝ) - 1/((x:ℝ)^((1:ℝ)/10) - 1)
      ≤ Real.log ((x:ℝ)^((1:ℝ)/10) - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hTpos hTm1pos)
    rw [Real.log_div hTne hTm1ne] at h
    have hsub : (x:ℝ)^((1:ℝ)/10) / ((x:ℝ)^((1:ℝ)/10) - 1) - 1
        = 1/((x:ℝ)^((1:ℝ)/10) - 1) := by
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
  have hlogXge : 10 * Real.log (10/δ) ≤ Real.log (x:ℝ) := by
    have h := Real.log_le_log (pow_pos hdpos 10) hx
    rwa [Real.log_pow] at h
  -- the two small error terms
  have hA : 1/((x:ℝ)^((1:ℝ)/10) - 1) ≤ δ/9 := by
    have hpos : 0 < (10:ℝ)/δ - 1 := by linarith
    have hge : (10:ℝ)/δ - 1 ≤ (x:ℝ)^((1:ℝ)/10) - 1 := by linarith
    have h1 := one_div_le_one_div_of_le hpos hge
    have heq : 1/((10:ℝ)/δ - 1) = δ/(10-δ) := by field_simp; try ring
    have h2 : δ/(10-δ) ≤ δ/9 := div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
    linarith
  have hXge10 : (10:ℝ)/δ ≤ (x:ℝ) := by
    have h : (10:ℝ)/δ ≤ ((10:ℝ)/δ)^10 := by
      simpa using pow_le_pow_right₀ (show (1:ℝ) ≤ 10/δ by linarith) (show 1 ≤ 10 by norm_num)
    linarith
  have hδX : (1:ℝ) ≤ δ * (x:ℝ) := by
    have h : δ * ((10:ℝ)/δ) ≤ δ * (x:ℝ) := mul_le_mul_of_nonneg_left hXge10 hδ.le
    have h2 : δ * ((10:ℝ)/δ) = 10 := by field_simp; try ring
    linarith
  have hinv : 1/(x:ℝ) ≤ δ := by
    rw [div_le_iff₀ hXpos]
    linarith
  have hB : ((1:ℝ)/10 - δ) * (2/(x:ℝ)) ≤ δ/5 := by
    have h1 : ((1:ℝ)/10 - δ) * (2/(x:ℝ)) ≤ (1/10) * (2/(x:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (div_pos (by norm_num) hXpos))
    have h2 : (1/10:ℝ) * (2/(x:ℝ)) = 1/(5*(x:ℝ)) := by field_simp; try ring
    have h3 : (1:ℝ)/(5*(x:ℝ)) = (1/5) * (1/(x:ℝ)) := by field_simp; try ring
    have h4 : (1/5) * (1/(x:ℝ)) ≤ (1/5) * δ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith
  -- the main numerical gain: `δ log x ≥ 5δ` beats both error terms
  have hC : 5*δ ≤ δ * Real.log (x:ℝ) := by
    have h5 : (5:ℝ) ≤ Real.log (x:ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_right h5 hδ.le
    linarith
  have hlogX2pos : 0 < Real.log ((x:ℝ)+2) := Real.log_pos (by linarith)
  rw [le_div_iff₀ hlogX2pos]
  have h2 : ((1:ℝ)/10 - δ) * Real.log ((x:ℝ)+2)
      ≤ ((1:ℝ)/10 - δ) * (Real.log (x:ℝ) + 2/(x:ℝ)) :=
    mul_le_mul_of_nonneg_left hlogX2 (by linarith)
  nlinarith [h2, hA, hB, hC, hstep, hlogM, hδ.le]

end Work.NumberTheory.Chen.BTermCount
