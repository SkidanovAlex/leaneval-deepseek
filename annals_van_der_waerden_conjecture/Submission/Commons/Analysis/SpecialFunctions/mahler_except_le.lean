import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 2000000

namespace Commons.Analysis.SpecialFunctions

/-- `m! ≤ m^(m-1)` for `m ≥ 1`. -/
lemma factorial_le_pow_pred (m : ℕ) (hm : 1 ≤ m) : m.factorial ≤ m ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · rw [Nat.factorial_succ]
      calc (k + 1) * k.factorial
          ≤ (k + 1) * k ^ (k - 1) := Nat.mul_le_mul_left _ (ih hk)
        _ ≤ (k + 1) * (k + 1) ^ (k - 1) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) _)
        _ = (k + 1) ^ ((k + 1) - 1) := by
              rw [Nat.succ_sub_one, ← pow_succ', Nat.sub_add_cancel hk]

/-- `(n-1)! ≤ n^(n-2)` for `n ≥ 2`. -/
lemma factorial_pred_le_pow (n : ℕ) (hn : 2 ≤ n) : (n - 1).factorial ≤ n ^ (n - 2) := by
  have h1 : 1 ≤ n - 1 := by omega
  calc (n - 1).factorial ≤ (n - 1) ^ ((n - 1) - 1) := factorial_le_pow_pred (n-1) h1
    _ ≤ n ^ (n - 2) := by
        have : (n - 1) - 1 = n - 2 := by omega
        rw [this]
        exact Nat.pow_le_pow_left (by omega) _

theorem mahler_except_le (n : ℕ) (hn : 2 ≤ n) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam4 : 4 ≤ lam) (hlamY : lam ≤ Y) :
    (25:ℝ) + (100:ℝ)^2 * (16 * Y / lam) * (1 + Real.log (16 * Y / lam))
      ≤ (5:ℝ)^n + (100:ℝ)^n * ((8:ℝ)^n * Y / lam) *
        (1 + Real.log ((8:ℝ)^n * Y / lam)) ^ (n - 1) / (((n-1).factorial : ℕ) : ℝ) := by
  have hlampos : 0 < lam := by linarith
  have hYpos : 0 < Y := by linarith
  have hrpos : 0 < Y / lam := by positivity
  have hr1 : 1 ≤ Y / lam := (one_le_div hlampos).mpr hlamY
  -- log 8 ≥ 1
  have hlog8 : (1:ℝ) ≤ Real.log 8 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 8)]
    linarith [Real.exp_one_lt_three]
  -- 16 ≤ 8^n
  have h16le8n : (16:ℝ) ≤ (8:ℝ)^n := by
    have h : (8:ℝ)^2 ≤ (8:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h ⊢
    linarith
  -- abbreviations
  set B : ℝ := 1 + Real.log (16 * Y / lam) with hB
  set A : ℝ := 1 + Real.log ((8:ℝ)^n * Y / lam) with hA
  -- B is positive
  have h16div1 : (1:ℝ) ≤ 16 * Y / lam := by
    rw [show 16 * Y / lam = 16 * (Y/lam) by ring]
    have h := mul_le_mul (by norm_num : (1:ℝ) ≤ 16) hr1 (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) ≤ 16)
    simpa using h
  have hB0 : 0 ≤ B := by
    rw [hB]
    have := Real.log_nonneg h16div1
    linarith
  -- log decomposition
  have hlog8n : Real.log ((8:ℝ)^n * Y / lam)
      = (n:ℝ) * Real.log 8 + Real.log (Y/lam) := by
    rw [show (8:ℝ)^n * Y / lam = (8:ℝ)^n * (Y/lam) by ring]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  -- A ≥ n
  have hAn : (n:ℝ) ≤ A := by
    rw [hA, hlog8n]
    have h1 : (n:ℝ) * 1 ≤ (n:ℝ) * Real.log 8 :=
      mul_le_mul_of_nonneg_left hlog8 (by positivity)
    have h2 : 0 ≤ Real.log (Y/lam) := Real.log_nonneg hr1
    nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hAn
  -- B ≤ A
  have hBA : B ≤ A := by
    rw [hB, hA]
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    rw [show 16 * Y / lam = 16 * (Y/lam) by ring,
        show (8:ℝ)^n * Y / lam = (8:ℝ)^n * (Y/lam) by ring]
    exact mul_le_mul_of_nonneg_right h16le8n (le_of_lt hrpos)
  -- A^{n-1} ≥ n^{n-2} * B
  have hApow : (n:ℝ)^(n-2) * B ≤ A^(n-1) := by
    have hpow : (n:ℝ)^(n-2) ≤ A^(n-2) :=
      pow_le_pow_left₀ (by positivity) hAn (n-2)
    calc (n:ℝ)^(n-2) * B ≤ A^(n-2) * B := mul_le_mul_of_nonneg_right hpow hB0
      _ ≤ A^(n-2) * A := mul_le_mul_of_nonneg_left hBA (by positivity)
      _ = A^(n-1) := by rw [show n - 1 = (n-2) + 1 by omega, pow_succ]
  -- factorial bound
  have hnfac : (((n-1).factorial:ℕ):ℝ) ≤ (n:ℝ)^(n-2) := by
    have := factorial_pred_le_pow n hn
    exact_mod_cast this
  have hfacpos : (0:ℝ) < (((n-1).factorial:ℕ):ℝ) := by
    exact_mod_cast Nat.factorial_pos (n-1)
  -- 160000 ≤ 800^n
  have h800 : (160000:ℝ) ≤ (800:ℝ)^n := by
    have h : (800:ℝ)^2 ≤ (800:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h
    linarith
  -- chain
  have hchain : (160000:ℝ) * B * (((n-1).factorial:ℕ):ℝ) ≤ (800:ℝ)^n * A^(n-1) := by
    have h1 : (160000:ℝ) * B * (((n-1).factorial:ℕ):ℝ)
        ≤ (160000:ℝ) * B * (n:ℝ)^(n-2) :=
      mul_le_mul_of_nonneg_left hnfac (by positivity)
    have h2 : (160000:ℝ) * B * (n:ℝ)^(n-2) ≤ (800:ℝ)^n * ((n:ℝ)^(n-2) * B) := by
      have hb : 0 ≤ (n:ℝ)^(n-2) * B := by positivity
      have := mul_le_mul_of_nonneg_right h800 hb
      linarith [this]
    have h3 : (800:ℝ)^n * ((n:ℝ)^(n-2) * B) ≤ (800:ℝ)^n * A^(n-1) :=
      mul_le_mul_of_nonneg_left hApow (by positivity)
    linarith [h1, h2, h3]
  have hh : (160000:ℝ) * B ≤ (800:ℝ)^n * A^(n-1) / (((n-1).factorial:ℕ):ℝ) := by
    rw [le_div_iff₀ hfacpos]
    exact hchain
  -- main term inequality
  have hmain : (100:ℝ)^2 * (16 * Y / lam) * B
      ≤ (100:ℝ)^n * ((8:ℝ)^n * Y / lam) * A^(n-1) / (((n-1).factorial:ℕ):ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hh (le_of_lt hrpos)
    calc (100:ℝ)^2 * (16 * Y / lam) * B
        = (Y/lam) * (160000 * B) := by ring
      _ ≤ (Y/lam) * ((800:ℝ)^n * A^(n-1) / (((n-1).factorial:ℕ):ℝ)) := hmul
      _ = (100:ℝ)^n * ((8:ℝ)^n * Y / lam) * A^(n-1) / (((n-1).factorial:ℕ):ℝ) := by
          have h800eq : (800:ℝ)^n = (100:ℝ)^n * (8:ℝ)^n := by
            rw [show (800:ℝ) = 100 * 8 by norm_num, mul_pow]
          rw [h800eq]; ring
  -- 25 ≤ 5^n
  have h5 : (25:ℝ) ≤ (5:ℝ)^n := by
    have h : (5:ℝ)^2 ≤ (5:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h
    linarith
  exact add_le_add h5 hmain

end Commons.Analysis.SpecialFunctions