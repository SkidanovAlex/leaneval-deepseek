import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.SpecialFunctions.pow_two_mul_pred_le_factorial

set_option maxHeartbeats 4000000

namespace Commons.Analysis.SpecialFunctions

theorem mahler_arith_large_lam (n : ℕ) (hn : 2 ≤ n) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam1 : 1 ≤ lam) (hlam4 : 4 ≤ lam) (hlamY : lam ≤ Y) :
    (2:ℝ)^n * ((5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
        (1 + Real.log ((8:ℝ)^n * Y / lam)) ^ (n - 1) / (((n-1).factorial : ℕ) : ℝ))
      + (16 * Y / lam) * (1 + Real.log (4 * Y / lam)) + 8 * Y / lam
      ≤ (100000:ℝ)^n * Y * (1 + Real.log Y)^(n-1) / lam := by
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY
  have hlampos : 0 < lam := by linarith
  have hn1 : 1 ≤ n := by omega
  have hnml : 1 ≤ n - 1 := by omega
  have hnr : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnnonneg : (0:ℝ) ≤ (n:ℝ) := by positivity
  -- abbreviations
  set a : ℝ := 1 + Real.log Y with ha
  set b : ℝ := 1 + Real.log ((8:ℝ)^n * Y / lam) with hb
  set c : ℝ := 1 + Real.log (4 * Y / lam) with hc
  have ha1 : (1:ℝ) ≤ a := by rw [ha]; have := Real.log_nonneg hY; linarith
  have ha0 : (0:ℝ) ≤ a := le_trans zero_le_one ha1
  have hapow1 : (1:ℝ) ≤ a^(n-1) := one_le_pow₀ ha1
  have hYdiv1 : (1:ℝ) ≤ Y/lam := (one_le_div hlampos).mpr hlamY
  have hYdiv0 : (0:ℝ) ≤ Y/lam := le_trans zero_le_one hYdiv1
  -- log 8 ≤ 3
  have hlog8 : Real.log (8:ℝ) ≤ 3 := by
    have h2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
      linarith [Real.exp_one_gt_two]
    have heq : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      push_cast; ring
    rw [heq]; linarith
  -- b ≤ 4 n a
  have hb_bound1 : b ≤ 1 + (n:ℝ) * Real.log 8 + Real.log Y := by
    rw [hb]
    have h8n_pos : (0:ℝ) < (8:ℝ)^n := by positivity
    have hYdiv_pos : 0 < Y / lam := by positivity
    have hlogYdiv : Real.log (Y/lam) ≤ Real.log Y := by
      apply Real.log_le_log hYdiv_pos
      rw [div_le_iff₀ hlampos]
      nlinarith [hYpos, hlam1]
    have hlogpow : Real.log ((8:ℝ)^n) = (n:ℝ) * Real.log 8 := Real.log_pow (8:ℝ) n
    have hsplit : Real.log ((8:ℝ)^n * Y / lam) = Real.log ((8:ℝ)^n) + Real.log (Y/lam) := by
      rw [show (8:ℝ)^n * Y / lam = (8:ℝ)^n * (Y/lam) by ring]
      rw [Real.log_mul (ne_of_gt h8n_pos) (ne_of_gt hYdiv_pos)]
    rw [hsplit, hlogpow]
    linarith
  have hb_le : b ≤ 4 * (n:ℝ) * a := by
    rw [ha]
    have hnl8 : (n:ℝ) * Real.log 8 ≤ 3 * (n:ℝ) := by
      calc (n:ℝ) * Real.log 8 ≤ (n:ℝ) * 3 := mul_le_mul_of_nonneg_left hlog8 hnnonneg
        _ = 3 * (n:ℝ) := by ring
    have hlogYnn : 0 ≤ Real.log Y := Real.log_nonneg hY
    have h4 : (0:ℝ) ≤ (4 * (n:ℝ) - 1) * Real.log Y :=
      mul_nonneg (by nlinarith [hnr]) hlogYnn
    linarith [hb_bound1, hnl8, h4]
  have hb0 : (0:ℝ) ≤ b := by
    have h8n1 : (1:ℝ) ≤ (8:ℝ)^n := one_le_pow₀ (by norm_num)
    have hprod : (1:ℝ) ≤ (8:ℝ)^n * Y / lam := by
      have h : (8:ℝ)^n * Y / lam = (8:ℝ)^n * (Y/lam) := by ring
      rw [h]
      have := mul_le_mul h8n1 hYdiv1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (8:ℝ)^n)
      simpa using this
    have := Real.log_nonneg hprod
    rw [hb]; linarith
  -- b^(n-1) bound
  have hbpow : b^(n-1) ≤ (12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) * a^(n-1) := by
    have h4n : (4 * (n:ℝ))^(n-1) ≤ (12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) := by
      have hnf : (n:ℝ)^(n-1) ≤ (3:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) := by
        have h : ((n^(n-1) : ℕ) : ℝ) ≤ ((3^(n-1) * (n-1).factorial : ℕ) : ℝ) := by
          exact_mod_cast pow_pred_le_three_pow_mul_factorial n hn1
        push_cast at h ⊢
        exact h
      rw [show (4 * (n:ℝ))^(n-1) = (4:ℝ)^(n-1) * (n:ℝ)^(n-1) by rw [mul_pow]]
      calc (4:ℝ)^(n-1) * (n:ℝ)^(n-1)
          ≤ (4:ℝ)^(n-1) * ((3:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ)) :=
            mul_le_mul_of_nonneg_left hnf (by positivity)
        _ = (12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) := by
            rw [← mul_assoc, ← mul_pow]; norm_num
    have h1 : b^(n-1) ≤ (4 * (n:ℝ) * a)^(n-1) := pow_le_pow_left₀ hb0 hb_le (n-1)
    calc b^(n-1) ≤ (4 * (n:ℝ) * a)^(n-1) := h1
      _ = (4 * (n:ℝ))^(n-1) * a^(n-1) := by rw [mul_pow]
      _ ≤ ((12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ)) * a^(n-1) :=
            mul_le_mul_of_nonneg_right h4n (by positivity)
      _ = (12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) * a^(n-1) := by ring
  have hfacpos : (0:ℝ) < (((n-1).factorial:ℕ):ℝ) := by exact_mod_cast Nat.factorial_pos (n-1)
  have hbdiv : b^(n-1) / (((n-1).factorial:ℕ):ℝ) ≤ (12:ℝ)^(n-1) * a^(n-1) := by
    rw [div_le_iff₀ hfacpos]
    calc b^(n-1) ≤ (12:ℝ)^(n-1) * (((n-1).factorial:ℕ):ℝ) * a^(n-1) := hbpow
      _ = ((12:ℝ)^(n-1) * a^(n-1)) * (((n-1).factorial:ℕ):ℝ) := by ring
  -- constant inequality 3·12^(n-1) ≤ 62.5^n and 1600^n·12^(n-1) ≤ 100000^n/3
  have h125 : (3:ℝ) ≤ (125/24:ℝ)^n := by
    have h2 : (125/24:ℝ)^2 ≤ (125/24:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith [h2]
  have h3_12n : (3:ℝ) * 12^n ≤ 62.5^n := by
    have heq : (62.5:ℝ)^n = (125/24:ℝ)^n * 12^n := by
      rw [show (62.5:ℝ) = 125/24 * 12 by norm_num, mul_pow]
    rw [heq]
    have h12n : (0:ℝ) ≤ 12^n := by positivity
    nlinarith [h125, h12n]
  have hconst : (1600:ℝ)^n * (12:ℝ)^(n-1) ≤ (100000:ℝ)^n/3 := by
    have h12pred : (12:ℝ)^(n-1) ≤ (12:ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega : n-1 ≤ n)
    have hleft : (3:ℝ) * (12:ℝ)^(n-1) ≤ (62.5:ℝ)^n := by
      have h := mul_le_mul_of_nonneg_left h12pred (by norm_num : (0:ℝ) ≤ 3)
      linarith [h, h3_12n]
    have h1600 : (0:ℝ) ≤ (1600:ℝ)^n := by positivity
    have hmul := mul_le_mul_of_nonneg_left hleft h1600
    have hpow : (100000:ℝ)^n = (1600:ℝ)^n * (62.5:ℝ)^n := by
      rw [show (100000:ℝ) = 1600 * 62.5 by norm_num, mul_pow]
    rw [hpow]
    nlinarith [hmul]
  -- Term A
  have hA : (2:ℝ)^n * (5:ℝ)^n ≤ (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by
    have h25 : (2:ℝ)^n * (5:ℝ)^n = (10:ℝ)^n := by rw [← mul_pow]; norm_num
    rw [h25]
    have h10 : (10:ℝ)^n ≤ (100000:ℝ)^n/3 := by
      have h3 : (3:ℝ) ≤ (10000:ℝ)^n := by
        have h2 : (10000:ℝ)^1 ≤ 10000^n := pow_le_pow_right₀ (by norm_num) hn1
        rw [pow_one] at h2; linarith
      have hpow : (100000:ℝ)^n = (10:ℝ)^n * (10000:ℝ)^n := by
        rw [show (100000:ℝ) = 10 * 10000 by norm_num, mul_pow]
      rw [hpow]
      have h10p : (0:ℝ) < (10:ℝ)^n := by positivity
      nlinarith [h3, h10p]
    have hQ1 : (1:ℝ) ≤ (Y/lam) * a^(n-1) := by
      have := mul_le_mul hYdiv1 hapow1 (by norm_num : (0:ℝ) ≤ 1) hYdiv0
      simpa using this
    have hcoef : (0:ℝ) ≤ (100000:ℝ)^n/3 := by positivity
    calc (10:ℝ)^n ≤ (100000:ℝ)^n/3 := h10
      _ ≤ (100000:ℝ)^n/3 * ((Y/lam)*a^(n-1)) := le_mul_of_one_le_right hcoef hQ1
      _ = (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by ring
  -- Term B
  have hB : (2:ℝ)^n * ((100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ))
      ≤ (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by
    have h1600 : (2:ℝ)^n * (100:ℝ)^n * (8:ℝ)^n = (1600:ℝ)^n := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have hrew : (2:ℝ)^n * ((100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ))
        = (Y/lam) * (1600:ℝ)^n * (b^(n-1) / (((n-1).factorial:ℕ):ℝ)) := by
      rw [show (2:ℝ)^n * ((100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ))
          = (2:ℝ)^n * (100:ℝ)^n * (8:ℝ)^n * (Y/lam) * (b^(n-1) / (((n-1).factorial:ℕ):ℝ)) by ring]
      rw [h1600]; ring
    rw [hrew]
    calc (Y/lam) * (1600:ℝ)^n * (b^(n-1) / (((n-1).factorial:ℕ):ℝ))
        ≤ (Y/lam) * (1600:ℝ)^n * ((12:ℝ)^(n-1) * a^(n-1)) := by
          apply mul_le_mul_of_nonneg_left hbdiv
          positivity
      _ = ((1600:ℝ)^n * (12:ℝ)^(n-1)) * ((Y/lam) * a^(n-1)) := by ring
      _ ≤ ((100000:ℝ)^n/3) * ((Y/lam) * a^(n-1)) :=
            mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by ring
  -- Term C
  have hc_le_a : c ≤ a := by
    rw [hc, ha]
    have h4Ylam_pos : 0 < 4*Y/lam := by positivity
    have hle : 4*Y/lam ≤ Y := by
      rw [div_le_iff₀ hlampos]; nlinarith [hYpos, hlam4]
    have := Real.log_le_log h4Ylam_pos hle
    linarith
  have hC : (16 * Y / lam) * c + 8 * Y / lam ≤ (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by
    have h24 : (24:ℝ) ≤ (100000:ℝ)^n/3 := by
      have h3 : (72:ℝ) ≤ (100000:ℝ)^n := by
        have h2 : (100000:ℝ)^2 ≤ (100000:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
        nlinarith [h2]
      linarith
    have hap_ge_a : a ≤ a^(n-1) := by
      have h2 : a^1 ≤ a^(n-1) := pow_le_pow_right₀ ha1 hnml
      simpa using h2
    have hinner : 16*c + 8 ≤ (100000:ℝ)^n/3 * a^(n-1) := by
      have h1 : 16*c + 8 ≤ 16*a + 8 := by linarith [hc_le_a]
      have h2 : 16*a + 8 ≤ 24*a := by linarith [ha1]
      have h3 : (24:ℝ)*a ≤ ((100000:ℝ)^n/3) * a^(n-1) := by
        calc (24:ℝ)*a ≤ ((100000:ℝ)^n/3) * a := mul_le_mul_of_nonneg_right h24 ha0
          _ ≤ ((100000:ℝ)^n/3) * a^(n-1) := mul_le_mul_of_nonneg_left hap_ge_a (by positivity)
      linarith
    have hfac : (16*Y/lam)*c + 8*Y/lam = (Y/lam)*(16*c+8) := by ring
    rw [hfac]
    calc (Y/lam)*(16*c+8) ≤ (Y/lam)*((100000:ℝ)^n/3 * a^(n-1)) := mul_le_mul_of_nonneg_left hinner hYdiv0
      _ = (100000:ℝ)^n/3 * (Y/lam) * a^(n-1) := by ring
  -- assembly
  have hRHS : (100000:ℝ)^n * Y * a^(n-1) / lam = (100000:ℝ)^n * (Y/lam) * a^(n-1) := by ring
  have hexp : (2:ℝ)^n * ((5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ))
      = (2:ℝ)^n * (5:ℝ)^n
        + (2:ℝ)^n * ((100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ)) := by ring
  rw [hRHS, hexp]
  have hsum : (2:ℝ)^n * (5:ℝ)^n
        + (2:ℝ)^n * ((100:ℝ)^n * ((8:ℝ)^n * Y / lam) * b^(n-1) / (((n-1).factorial:ℕ):ℝ))
        + ((16 * Y / lam) * c + 8 * Y / lam)
      ≤ 3 * ((100000:ℝ)^n/3 * (Y/lam) * a^(n-1)) := by linarith [hA, hB, hC]
  have hthree : 3 * ((100000:ℝ)^n/3 * (Y/lam) * a^(n-1)) = (100000:ℝ)^n * (Y/lam) * a^(n-1) := by ring
  linarith [hsum, hthree]

end Commons.Analysis.SpecialFunctions