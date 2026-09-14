import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace Commons.Analysis.SpecialFunctions

open Real

/-- `Real.log 8 ≤ 3`. -/
lemma mahler_small_lam_log8_le_three : Real.log 8 ≤ 3 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    have h8 : (8:ℝ) = 2^3 := by norm_num
    rw [h8, Real.log_pow]; push_cast; ring
  rw [h]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

/-- `Real.exp 1 < 3`. -/
lemma mahler_small_lam_exp_one_lt_three : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9
  linarith

/--
Arithmetic core: for `m ≥ 1`,
`1/8 + (1 + (m+1) * log 8)^m / m! ≤ 125^(m+1)`.
-/
lemma mahler_small_lam_arith_aux (m : ℕ) (hm : 1 ≤ m) :
    (1:ℝ)/8 + (1 + ((m:ℝ)+1) * Real.log 8)^m / (((m.factorial:ℕ):ℝ)) ≤ (125:ℝ)^(m+1) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog8nn : (0:ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hst := Stirling.le_factorial_stirling m
  have hsqrt : (1:ℝ) ≤ Real.sqrt (2 * Real.pi * (m:ℝ)) := by
    rw [Real.one_le_sqrt]
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three, hm1]
  have hB : ((m:ℝ)/Real.exp 1)^m ≤ ((m.factorial:ℕ):ℝ) := by
    have h2 : ((m:ℝ)/Real.exp 1)^m ≤ Real.sqrt (2 * Real.pi * (m:ℝ)) * ((m:ℝ)/Real.exp 1)^m := by
      have h3 := mul_le_mul_of_nonneg_right hsqrt (pow_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)/Real.exp 1) m)
      simpa using h3
    linarith [hst]
  have hbase : 1 + ((m:ℝ)+1) * Real.log 8 ≤ 7*(m:ℝ) := by
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith [mahler_small_lam_log8_le_three, hm1, hlog8nn]
  have hbasenn : (0:ℝ) ≤ 1 + ((m:ℝ)+1) * Real.log 8 := by nlinarith [hm0, hlog8nn]
  have hp : (1 + ((m:ℝ)+1) * Real.log 8)^m ≤ (7*(m:ℝ))^m :=
    pow_le_pow_left₀ hbasenn hbase m
  have hFpos : 0 < ((m.factorial:ℕ):ℝ) := by positivity
  have hBpos : 0 < (m:ℝ)/Real.exp 1 := by positivity
  have hBmpos : 0 < ((m:ℝ)/Real.exp 1)^m := pow_pos hBpos m
  have hinv : 1/ ((m.factorial:ℕ):ℝ) ≤ 1/((m:ℝ)/Real.exp 1)^m :=
    one_div_le_one_div_of_le hBmpos hB
  have hdiv : (7*(m:ℝ))^m / ((m.factorial:ℕ):ℝ) ≤ (7*Real.exp 1)^m := by
    rw [div_eq_mul_one_div]
    calc (7*(m:ℝ))^m * (1/((m.factorial:ℕ):ℝ))
        ≤ (7*(m:ℝ))^m * (1/((m:ℝ)/Real.exp 1)^m) :=
          mul_le_mul_of_nonneg_left hinv (pow_nonneg (by positivity : (0:ℝ) ≤ 7*(m:ℝ)) m)
      _ = (7*Real.exp 1)^m := by
          rw [mul_one_div, ← div_pow]
          congr 1
          field_simp
  have h7e : (7*Real.exp 1)^m ≤ (125:ℝ)^m := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mahler_small_lam_exp_one_lt_three]
  have h125 : (1:ℝ)/8 + (125:ℝ)^m ≤ (125:ℝ)^(m+1) := by
    have hpow : (125:ℝ) ≤ (125:ℝ)^m := by
      calc (125:ℝ) = (125:ℝ)^1 := by ring
        _ ≤ (125:ℝ)^m := pow_le_pow_right₀ (by norm_num) hm
    have : (125:ℝ)^(m+1) = (125:ℝ)^m * 125 := by rw [pow_succ]
    rw [this]
    nlinarith [hpow]
  calc (1:ℝ)/8 + (1 + ((m:ℝ)+1) * Real.log 8)^m / (((m.factorial:ℕ):ℝ))
      ≤ (1:ℝ)/8 + (7*(m:ℝ))^m / (((m.factorial:ℕ):ℝ)) := by
        have := div_le_div_of_nonneg_right hp hFpos.le
        linarith
    _ ≤ (1:ℝ)/8 + (7*Real.exp 1)^m := by linarith
    _ ≤ (1:ℝ)/8 + (125:ℝ)^m := by linarith
    _ ≤ (125:ℝ)^(m+1) := h125

/-- `log ((8^n * Y)/lam) ≤ n * log 8 + log Y` for `Y ≥ 1`, `lam ≥ 1`. -/
lemma mahler_small_lam_log_shift (n : ℕ) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam1 : 1 ≤ lam) :
    Real.log ((8:ℝ)^n * Y / lam) ≤ (n:ℝ) * Real.log 8 + Real.log Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hUpos : 0 < (8:ℝ)^n * Y / lam := by positivity
  have hle : (8:ℝ)^n * Y / lam ≤ (8:ℝ)^n * Y := by
    apply div_le_self (by positivity) hlam1
  calc Real.log ((8:ℝ)^n * Y / lam) ≤ Real.log ((8:ℝ)^n * Y) := Real.log_le_log hUpos hle
    _ = Real.log ((8:ℝ)^n) + Real.log Y := by
        rw [Real.log_mul (by positivity) (ne_of_gt hY0)]
    _ = (n:ℝ) * Real.log 8 + Real.log Y := by rw [Real.log_pow]

/--
Main reduction: if `U ≥ 16`, `Y ≥ 1` and `log U ≤ n * log 8 + log Y`, then
`5^n + 100^n * U * (1 + log U)^(n-1)/(n-1)! ≤ 100^n * 125^n * U * (1 + log Y)^(n-1)`.
-/
lemma mahler_small_lam_factor_bound (n : ℕ) (hn : 2 ≤ n) (U Y : ℝ) (hU : 16 ≤ U) (hY : 1 ≤ Y)
    (hlogU : Real.log U ≤ (n:ℝ)*Real.log 8 + Real.log Y) :
    (5:ℝ)^n + (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / (((n-1).factorial:ℕ):ℝ)
      ≤ (100:ℝ)^n * (125:ℝ)^n * U * (1 + Real.log Y)^(n-1) := by
  have hn1 : 1 ≤ n := by omega
  have hUpos : 0 < U := by linarith
  have hUnn : 0 ≤ U := le_of_lt hUpos
  have hlogYnn : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlog8nn : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogUnn : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hn8nn : 0 ≤ (n:ℝ)*Real.log 8 := mul_nonneg (by positivity) hlog8nn
  have hlogU1 : 0 ≤ 1 + Real.log U := by linarith
  set P := (1 + (n:ℝ)*Real.log 8)^(n-1) with hP
  set F := (((n-1).factorial:ℕ):ℝ) with hF
  set C := (1 + Real.log Y)^(n-1) with hC
  set W := (100:ℝ)^n * U * C with hW
  have hFpos : 0 < F := by rw [hF]; positivity
  have hC1 : 1 ≤ C := by rw [hC]; exact one_le_pow₀ (by linarith)
  have hWnn : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) hUnn) (le_trans zero_le_one hC1)
  have hpowbound : (1 + Real.log U)^(n-1) ≤ P * C := by
    have h1log : 1 + Real.log U ≤ (1 + (n:ℝ)*Real.log 8) * (1 + Real.log Y) := by
      nlinarith [hlogU, hlogYnn, hlogUnn, hn8nn]
    have := pow_le_pow_left₀ hlogU1 h1log (n-1)
    rw [mul_pow] at this
    rw [← hP, ← hC] at this
    exact this
  have hT : (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / F ≤ W * (P / F) := by
    have step1 : (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / F ≤ (100:ℝ)^n * U * (P*C) / F := by
      apply div_le_div_of_nonneg_right _ hFpos.le
      exact mul_le_mul_of_nonneg_left hpowbound (by positivity : (0:ℝ) ≤ (100:ℝ)^n * U)
    have heq : (100:ℝ)^n * U * (P*C)/F = W*(P/F) := by
      rw [hW]; field_simp
    rw [heq] at step1; exact step1
  have h5 : (5:ℝ)^n ≤ W * (1/8) := by
    have hCU : (2:ℝ)*(100:ℝ)^n ≤ (100:ℝ)^n * U * C / 8 := by
      rw [show (2:ℝ)*(100:ℝ)^n = (100:ℝ)^n*16/8 by ring]
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 8)
      calc (100:ℝ)^n*16 = (100:ℝ)^n*16*1 := by ring
        _ ≤ (100:ℝ)^n*U*C := by gcongr
    have h5100 : (5:ℝ)^n ≤ 2*(100:ℝ)^n := by
      have h1 : (5:ℝ)^n ≤ (100:ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      have h2 : (0:ℝ) ≤ (100:ℝ)^n := pow_nonneg (by norm_num) n
      linarith
    rw [hW, mul_one_div]
    linarith
  have hAF : (1:ℝ)/8 + P / F ≤ (125:ℝ)^n := by
    have hnm1 : 1 ≤ n - 1 := by omega
    have hcast : (((n-1:ℕ):ℝ) + 1) = (n:ℝ) := by
      have h2 : n - 1 + 1 = n := Nat.sub_add_cancel hn1
      rw [← h2]; push_cast; ring
    have h := mahler_small_lam_arith_aux (n-1) hnm1
    rw [hcast] at h
    rw [Nat.sub_add_cancel hn1] at h
    rw [← hP, ← hF] at h
    exact h
  have hgoal : (5:ℝ)^n + (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / F ≤ W*(125:ℝ)^n := by
    nlinarith [hT, h5, hAF, hWnn]
  calc (5:ℝ)^n + (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / (((n-1).factorial:ℕ):ℝ)
      = (5:ℝ)^n + (100:ℝ)^n * U * (1 + Real.log U)^(n-1) / F := by rw [hF]
    _ ≤ W*(125:ℝ)^n := hgoal
    _ = (100:ℝ)^n * (125:ℝ)^n * U * (1 + Real.log Y)^(n-1) := by rw [hW, hC]; ring

theorem mahler_arith_small_lam (n : ℕ) (hn : 2 ≤ n) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam1 : 1 ≤ lam) (hlam4 : lam ≤ 4) :
    (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
        (1 + Real.log ((8:ℝ)^n * Y / lam)) ^ (n - 1) / (((n-1).factorial : ℕ) : ℝ)
      ≤ (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
  have h8n : (64:ℝ) ≤ (8:ℝ)^n := by
    have := pow_le_pow_right₀ (show (1:ℝ) ≤ 8 by norm_num) hn
    have h2 : (8:ℝ)^2 = 64 := by norm_num
    rwa [h2] at this
  have h8nY : (64:ℝ) ≤ (8:ℝ)^n * Y := by
    have := mul_le_mul h8n hY (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (8:ℝ)^n)
    simpa using this
  have hU16 : (16:ℝ) ≤ (8:ℝ)^n * Y / lam := by
    have h1 : (8:ℝ)^n * Y / 4 ≤ (8:ℝ)^n * Y / lam :=
      div_le_div_of_nonneg_left (by positivity) hlam0 hlam4
    calc (16:ℝ) = 64/4 := by norm_num
      _ ≤ (8:ℝ)^n*Y/4 := div_le_div_of_nonneg_right h8nY (by norm_num)
      _ ≤ (8:ℝ)^n*Y/lam := h1
  have hlogU := mahler_small_lam_log_shift n Y lam hY hlam1
  have hfb := mahler_small_lam_factor_bound n hn ((8:ℝ)^n * Y / lam) Y hU16 hY hlogU
  calc (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
        (1 + Real.log ((8:ℝ)^n * Y / lam)) ^ (n - 1) / (((n-1).factorial : ℕ) : ℝ)
      ≤ (100:ℝ)^n * (125:ℝ)^n * ((8:ℝ)^n * Y / lam) * (1 + Real.log Y)^(n-1) := hfb
    _ = (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam := by
        have hpw : (100:ℝ)^n*(125:ℝ)^n*(8:ℝ)^n = (100000:ℝ)^n := by
          rw [← mul_pow, ← mul_pow]; norm_num
        calc (100:ℝ)^n*(125:ℝ)^n*((8:ℝ)^n*Y/lam)*(1+Real.log Y)^(n-1)
            = ((100:ℝ)^n*(125:ℝ)^n*(8:ℝ)^n) * (Y/lam) * (1+Real.log Y)^(n-1) := by ring
          _ = (100000:ℝ)^n * (Y/lam) * (1+Real.log Y)^(n-1) := by rw [hpw]
          _ = (100000:ℝ)^n * Y * (1+Real.log Y)^(n-1) / lam := by ring

end Commons.Analysis.SpecialFunctions