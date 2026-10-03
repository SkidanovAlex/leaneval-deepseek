import Mathlib

namespace Work.FIArea7

/-- Purely numerical inequality used in Area 7: for `N ≥ exp 250` and `1 ≤ X`,
`X ^ 9 ≤ N`,
```
1920000 * X * N ^ (7/4) * (log (2 + N)) ^ 4 ≤ 10 ^ 14 * X⁻¹ * N ^ 2 * log N
```
-/
theorem strip_numeric (N X : ℝ) (hN : Real.exp 250 ≤ N) (hX : 1 ≤ X) (hX9 : X ^ 9 ≤ N) :
    1920000 * X * N ^ ((7 : ℝ) / 4) * (Real.log (2 + N)) ^ 4
      ≤ 100000000000000 * X⁻¹ * N ^ 2 * Real.log N := by
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 250) hN
  have hN1 : (1:ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX
  have hXnn : 0 ≤ X := le_of_lt hXpos
  have hlogN : 250 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 250) hN
    rwa [Real.log_exp] at h
  have hlogNpos : 0 < Real.log N := lt_of_lt_of_le (by norm_num) hlogN
  -- Multiply both sides by the positive quantity `X`.
  rw [← mul_le_mul_iff_of_pos_right hXpos]
  have hL : 1920000 * X * N ^ ((7:ℝ)/4) * (Real.log (2+N))^4 * X
      = 1920000 * X^2 * N ^ ((7:ℝ)/4) * (Real.log (2+N))^4 := by ring
  have hR : 100000000000000 * X⁻¹ * N ^ 2 * Real.log N * X
      = 100000000000000 * N ^ 2 * Real.log N := by
    rw [show 100000000000000 * X⁻¹ * N ^ 2 * Real.log N * X
        = 100000000000000 * N^2 * Real.log N * (X⁻¹ * X) by ring]
    rw [inv_mul_cancel₀ (ne_of_gt hXpos), mul_one]
  rw [hL, hR]
  -- `X^2 ≤ N^(2/9)`, since `X^9 ≤ N`.
  have hX2 : X^2 ≤ N^((2:ℝ)/9) := by
    have h1 : X^2 = (X^9)^((2:ℝ)/9) := by
      rw [← Real.rpow_natCast_mul hXnn 9 ((2:ℝ)/9)]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (pow_nonneg hXnn 9) hX9 (by norm_num)
  have hNmul : N^((2:ℝ)/9) * N^((7:ℝ)/4) = N^((71:ℝ)/36) := by
    rw [← Real.rpow_add hNpos]; norm_num
  -- `log (2 + N) ≤ 2 log N`, hence `(log (2+N))^4 ≤ 16 (log N)^4`.
  have hL4 : (Real.log (2+N))^4 ≤ 16 * (Real.log N)^4 := by
    have h2N : (2:ℝ) + N ≤ 3 * N := by linarith
    have hlog_le : Real.log (2+N) ≤ Real.log (3*N) := Real.log_le_log (by linarith) h2N
    have hlog3N : Real.log (3*N) = Real.log 3 + Real.log N := Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hlog3 : Real.log 3 ≤ Real.log N := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
      linarith
    have hLle : Real.log (2+N) ≤ 2 * Real.log N := by linarith
    have hLnn : 0 ≤ Real.log (2+N) := Real.log_nonneg (by linarith)
    have h := pow_le_pow_left₀ hLnn hLle 4
    rw [mul_pow] at h; norm_num at h; exact h
  -- The exponential/Taylor estimate: `30720000 * (log N)^3 ≤ 10^14 * exp (log N / 36)`.
  have hExpBound : (30720000:ℝ) * (Real.log N)^3 ≤ 100000000000000 * Real.exp (Real.log N / 36) := by
    have h2 : (122880:ℝ) * (Real.log N)^4 ≤ 100000000000000 * ((Real.log N)^4/40310784) := by
      rw [show (122880:ℝ) * (Real.log N)^4 = (122880 * 40310784) * ((Real.log N)^4 / 40310784) by field_simp]
      exact mul_le_mul_of_nonneg_right (by norm_num : (122880:ℝ)*40310784 ≤ 100000000000000) (by positivity)
    have hexp : ((Real.log N)^4/40310784 : ℝ) ≤ Real.exp (Real.log N / 36) := by
      have h := Real.pow_div_factorial_le_exp (Real.log N / 36) (by positivity) 4
      norm_num at h
      have h24 : ((Real.log N / 36)^4/24 : ℝ) = (Real.log N)^4/40310784 := by ring
      rw [h24] at h; exact h
    have h1 : (30720000:ℝ) * (Real.log N)^3 ≤ 122880 * (Real.log N)^4 := by
      have h250 : (30720000:ℝ) ≤ 122880 * Real.log N := by nlinarith [hlogN]
      have h3 : (0:ℝ) ≤ (Real.log N)^3 := pow_nonneg (le_of_lt hlogNpos) 3
      have := mul_le_mul_of_nonneg_right h250 h3
      nlinarith [this]
    calc (30720000:ℝ)*(Real.log N)^3 ≤ 122880 * (Real.log N)^4 := h1
      _ ≤ 100000000000000 * ((Real.log N)^4/40310784) := h2
      _ ≤ 100000000000000 * Real.exp (Real.log N / 36) := mul_le_mul_of_nonneg_left hexp (by norm_num)
  have hN36 : N^((1:ℝ)/36) = Real.exp (Real.log N / 36) := by
    rw [Real.rpow_def_of_pos hNpos]; congr 1; ring
  have hkey : (30720000:ℝ) * (Real.log N)^3 ≤ 100000000000000 * N^((1:ℝ)/36) := by
    rw [hN36]; exact hExpBound
  have hNpow : N^((1:ℝ)/36) * N^((71:ℝ)/36) = N^2 := by
    rw [← Real.rpow_add hNpos]; norm_num
  -- Final numerical step: `30720000 * N^(71/36) * (log N)^4 ≤ 10^14 * N^2 * log N`.
  have hstep2 : (30720000:ℝ) * N^((71:ℝ)/36) * (Real.log N)^4 ≤ 100000000000000 * N^2 * Real.log N := by
    have hmult := mul_le_mul_of_nonneg_right hkey (mul_nonneg (le_of_lt hlogNpos) (Real.rpow_nonneg hNpos.le ((71:ℝ)/36)))
    have e1 : (30720000:ℝ) * (Real.log N)^3 * (Real.log N * N^((71:ℝ)/36)) = 30720000 * N^((71:ℝ)/36) * (Real.log N)^4 := by ring
    have e2 : (100000000000000:ℝ) * N^((1:ℝ)/36) * (Real.log N * N^((71:ℝ)/36)) = 100000000000000 * N^2 * Real.log N := by
      rw [show (100000000000000:ℝ) * N^((1:ℝ)/36) * (Real.log N * N^((71:ℝ)/36))
           = 100000000000000 * Real.log N * (N^((1:ℝ)/36) * N^((71:ℝ)/36)) by ring, hNpow]
      ring
    rw [e1, e2] at hmult
    exact hmult
  have hXn4nn : (0:ℝ) ≤ N^((7:ℝ)/4) := Real.rpow_nonneg hNpos.le _
  have hprod1' : X^2 * N^((7:ℝ)/4) ≤ N^((71:ℝ)/36) := by
    have hp := mul_le_mul_of_nonneg_right hX2 hXn4nn
    rwa [hNmul] at hp
  have hprod2 : (X^2 * N^((7:ℝ)/4)) * (Real.log (2+N))^4 ≤ N^((71:ℝ)/36) * (16 * (Real.log N)^4) :=
    mul_le_mul hprod1' hL4 (by positivity) (Real.rpow_nonneg hNpos.le _)
  have hbig : 1920000 * X^2 * N^((7:ℝ)/4) * (Real.log (2+N))^4 ≤ 30720000 * N^((71:ℝ)/36) * (Real.log N)^4 := by
    have hmul3 : (1920000:ℝ) * ((X^2 * N^((7:ℝ)/4)) * (Real.log (2+N))^4) ≤ 1920000 * (N^((71:ℝ)/36) * (16 * (Real.log N)^4)) :=
      mul_le_mul_of_nonneg_left hprod2 (by norm_num)
    have e1 : (1920000:ℝ) * ((X^2 * N^((7:ℝ)/4)) * (Real.log (2+N))^4) = 1920000 * X^2 * N^((7:ℝ)/4) * (Real.log (2+N))^4 := by ring
    have e2 : (1920000:ℝ) * (N^((71:ℝ)/36) * (16 * (Real.log N)^4)) = 30720000 * N^((71:ℝ)/36) * (Real.log N)^4 := by ring
    rw [e1, e2] at hmul3
    exact hmul3
  linarith [hbig, hstep2]

end Work.FIArea7
