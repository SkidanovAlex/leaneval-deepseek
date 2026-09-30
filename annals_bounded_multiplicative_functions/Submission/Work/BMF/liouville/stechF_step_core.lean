import Mathlib
import Submission.Work.BMF.liouville.vmvt_stechkin_defs
import Submission.Work.BMF.vmvt_setup
import Submission.Work.BMF.vmvt_step_ineq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The per-step arithmetic for the sharp (Stechkin) Vinogradov mean value iteration

The induction constant `stechF k r = exp (stechK·k·r·(k+r)·(1+log k))` grows by
`exp (stechK·k·(2r+k+1)·(1+log k))` when `r ↦ r+1` (`stechF_growth`).  This file proves that this
growth covers the coefficient produced by one application of the Vinogradov–Linnik recursion,
`8·k!·k⁶·A^E·2^{th k r}` with `A = pC·k³·log k + 2k + 7` and `E = 2kr + k(k−1)/2`.
-/

open scoped BigOperators

namespace Work.BMF.liouville

set_option maxHeartbeats 2000000

/-- `1/log 2 ≤ 2`. -/
lemma one_div_log_two_le_two : 1 / Real.log 2 ≤ 2 := by
  have h : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h' := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h'
    linarith
  have hpos : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) h
  rw [div_le_iff₀ hpos]
  linarith

/-- `log(pC+8)/log 2 + 4 + 8 ≤ stechK`. -/
lemma stechK_ge_exp_bound : Real.log (Work.BMF.pC + 8) / Real.log 2 + 4 + 8 ≤ stechK := by
  have hL8 : 0 < Real.log (Work.BMF.pC + 8) := Real.log_pos (by linarith [Work.BMF.pC_pos])
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 1 ≤ 2 * Real.log 2 := by
    have h := one_div_log_two_le_two
    rw [div_le_iff₀ hlog2] at h
    linarith
  have hdiv : Real.log (Work.BMF.pC + 8) / Real.log 2 ≤ 2 * Real.log (Work.BMF.pC + 8) := by
    rw [div_le_iff₀ hlog2]
    nlinarith only [h1, hL8]
  rw [stechK, Work.BMF.C0]
  nlinarith only [hdiv, hL8]

/-- `8 ≤ stechK`. -/
lemma eight_le_stechK : 8 ≤ stechK := by
  have hL8 : 0 ≤ Real.log (Work.BMF.pC + 8) :=
    le_of_lt (Real.log_pos (by linarith [Work.BMF.pC_pos]))
  rw [stechK, Work.BMF.C0]
  nlinarith only [hL8]

/-- **The per-step arithmetic.**  For `k ≥ 2`, `r ≥ 1`,
`log (8·k!·k⁶·A^E·2^{th k r}) ≤ stechK·k·(2r+k+1)·(1+log k)` with `A = pC·k³·log k + 2k + 7` and
`E = 2kr + k(k−1)/2`. -/
lemma stechF_step_core (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    Real.log (8 * ((k.factorial : ℕ) : ℝ) * (k : ℝ) ^ 6 *
        (Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
          ^ (2 * k * r + k * (k - 1) / 2) *
        (2 : ℝ) ^ (Work.BMF.th k r))
      ≤ stechK * (k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) * (1 + Real.log (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlog2L : Real.log 2 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) hk2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL8pos : 0 < Real.log (Work.BMF.pC + 8) := Real.log_pos (by linarith [Work.BMF.pC_pos])
  have hpCpos : 0 < Work.BMF.pC := Work.BMF.pC_pos
  have hApos : 0 < Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7 := by
    have h : 0 ≤ Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) := by positivity
    linarith
  have hfactpos : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- `A ≤ (pC+8)·k³·(log k + 1)` and hence `log A ≤ log(pC+8) + 4 log k`
  have hAle : Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7
      ≤ (Work.BMF.pC + 8) * (k : ℝ) ^ 3 * (Real.log (k : ℝ) + 1) := by
    have h8 : 2 * (k : ℝ) + 7 ≤ 8 * (k : ℝ) ^ 3 := by
      have h4 : 2 * (k : ℝ) + 7 ≤ 4 * (k : ℝ) ^ 2 := by
        nlinarith only [sq_nonneg ((k : ℝ) - 1), hk2]
      have h5 : 4 * (k : ℝ) ^ 2 ≤ 8 * (k : ℝ) ^ 3 := by
        nlinarith only [hk2, sq_nonneg (k : ℝ)]
      linarith
    nlinarith only [h8, hL0, hpCpos]
  have hlogA : Real.log (Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
      ≤ Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ) := by
    have h2 : 0 < (Work.BMF.pC + 8) * (k : ℝ) ^ 3 * (Real.log (k : ℝ) + 1) := by positivity
    have h1 : Real.log (Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
        ≤ Real.log ((Work.BMF.pC + 8) * (k : ℝ) ^ 3 * (Real.log (k : ℝ) + 1)) :=
      Real.log_le_log hApos hAle
    have h3 : Real.log ((Work.BMF.pC + 8) * (k : ℝ) ^ 3 * (Real.log (k : ℝ) + 1))
        = Real.log (Work.BMF.pC + 8) + 3 * Real.log (k : ℝ) + Real.log (Real.log (k : ℝ) + 1) := by
      rw [Real.log_mul (show (Work.BMF.pC + 8) * (k : ℝ) ^ 3 ≠ 0 by
              exact ne_of_gt (by positivity))
          (show Real.log (k : ℝ) + 1 ≠ 0 by exact ne_of_gt (by linarith)),
          Real.log_mul (show Work.BMF.pC + 8 ≠ 0 by exact ne_of_gt (by linarith [hpCpos]))
            (show (k : ℝ) ^ 3 ≠ 0 by exact ne_of_gt (by positivity)),
          Real.log_pow]
      ring
    have h4 : Real.log (Real.log (k : ℝ) + 1) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) (by linarith [Real.log_le_sub_one_of_pos hkpos])
    rw [h3] at h1
    linarith
  -- the log of the coefficient, split into five terms
  have hlogsplit : Real.log (8 * ((k.factorial : ℕ) : ℝ) * (k : ℝ) ^ 6 *
      (Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
        ^ (2 * k * r + k * (k - 1) / 2) *
      (2 : ℝ) ^ (Work.BMF.th k r))
      = Real.log 8 + Real.log ((k.factorial : ℕ) : ℝ) + Real.log ((k : ℝ) ^ 6)
        + Real.log ((Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
            ^ (2 * k * r + k * (k - 1) / 2))
        + Real.log ((2 : ℝ) ^ (Work.BMF.th k r)) :=
    Work.BMF.log_mul5 8 ((k.factorial : ℕ) : ℝ) ((k : ℝ) ^ 6)
      ((Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
        ^ (2 * k * r + k * (k - 1) / 2))
      ((2 : ℝ) ^ (Work.BMF.th k r))
      (by norm_num) hfactpos (by positivity) (pow_pos hApos _)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hfac : Real.log ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
    have h1 : ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
      calc ((k.factorial : ℕ) : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorial_le_pow k
        _ = (k : ℝ) ^ k := by push_cast; ring
    calc Real.log ((k.factorial : ℕ) : ℝ) ≤ Real.log ((k : ℝ) ^ k) :=
          Real.log_le_log hfactpos h1
      _ = (k : ℝ) * Real.log (k : ℝ) := Real.log_pow _ _
  have hlog8 : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  -- Step A: `log (coefficient) ≤ log 8 + k log k + 6 log k + E(log(pC+8) + 4 log k) + th·log 2`
  have hstepA : Real.log (8 * ((k.factorial : ℕ) : ℝ) * (k : ℝ) ^ 6 *
      (Work.BMF.pC * (k : ℝ) ^ 3 * Real.log (k : ℝ) + 2 * (k : ℝ) + 7)
        ^ (2 * k * r + k * (k - 1) / 2) *
      (2 : ℝ) ^ (Work.BMF.th k r))
      ≤ Real.log 8 + (k : ℝ) * Real.log (k : ℝ) + 6 * Real.log (k : ℝ)
        + ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ)
          * (Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ))
        + (Work.BMF.th k r) * Real.log 2 := by
    rw [hlogsplit, Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num)]
    have hE0 : (0 : ℝ) ≤ ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlogA hE0
    linarith
  -- Step B: pass to the sharper expressions `2kr + k²` and `Λ log k`
  have hstepB : Real.log 8 + (k : ℝ) * Real.log (k : ℝ) + 6 * Real.log (k : ℝ)
        + ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ)
          * (Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ))
        + (Work.BMF.th k r) * Real.log 2
      ≤ 7 + (k : ℝ) * Real.log (k : ℝ) + 6 * Real.log (k : ℝ)
        + (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
          * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ)
        + 2 * (k : ℝ) * (r : ℝ) * Real.log (k : ℝ) := by
    have hEbound : ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ) ≤ 2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2 := by
      have hdiv : ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
        have h2 : 2 ∣ k * (k - 1) := by
          rw [← even_iff_two_dvd]
          exact Nat.even_mul_pred_self k
        rw [Nat.cast_div (K := ℝ) h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hk1]
        ring
      have hmain : ((2 * k * r : ℕ) : ℝ) = 2 * (k : ℝ) * (r : ℝ) := by push_cast; ring
      rw [Nat.cast_add, hdiv, hmain]
      nlinarith only [hk2, sq_nonneg ((k : ℝ) - 1)]
    have hLam : Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ)
        ≤ (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ) := by
      have h1 : Real.log (Work.BMF.pC + 8) ≤ (Real.log (Work.BMF.pC + 8) / Real.log 2)
          * Real.log 2 := by
        rw [div_mul_cancel₀]
        exact ne_of_gt hlog2pos
      have h2 : (Real.log (Work.BMF.pC + 8) / Real.log 2) * Real.log 2
          ≤ (Real.log (Work.BMF.pC + 8) / Real.log 2) * Real.log (k : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2L (by positivity)
      nlinarith only [h1, h2, hL0]
    have hE0 : (0 : ℝ) ≤ ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ) := by positivity
    have hLam0 : 0 ≤ Real.log (Work.BMF.pC + 8) / Real.log 2 + 4 := by positivity
    have hbound2 : ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ)
          * (Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ))
        ≤ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
          * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ) := by
      have h2r : 0 ≤ 2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2 := by positivity
      calc ((2 * k * r + k * (k - 1) / 2 : ℕ) : ℝ)
            * (Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ))
          ≤ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
            * (Real.log (Work.BMF.pC + 8) + 4 * Real.log (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hEbound (by positivity)
        _ ≤ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
            * ((Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hLam h2r
        _ = (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
            * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ) := by ring
    have hth : (Work.BMF.th k r) * Real.log 2
        ≤ 2 * (k : ℝ) * (r : ℝ) * Real.log (k : ℝ) := by
      have h1 : Work.BMF.th k r ≤ 2 * (k : ℝ) * (r : ℝ) := Work.BMF.th_le_two_mul_aux k r hk1
      have h2 : 0 ≤ Work.BMF.th k r := le_of_lt (Work.BMF.th_pos_aux k r hk hr)
      have h4 : 0 ≤ 2 * (k : ℝ) * (r : ℝ) := by positivity
      calc (Work.BMF.th k r) * Real.log 2 ≤ (2 * (k : ℝ) * (r : ℝ)) * Real.log (k : ℝ) :=
            mul_le_mul h1 hlog2L (le_of_lt hlog2pos) h4
        _ = 2 * (k : ℝ) * (r : ℝ) * Real.log (k : ℝ) := by ring
    linarith only [hlog8, hbound2, hth]
  -- Step C: the resulting polynomial is dominated by `stechK k (2r+k+1)(1+log k)`
  have hlin : (k : ℝ) + 6 + (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
        * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) + 2 * (k : ℝ) * (r : ℝ)
      ≤ stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1)) := by
    have hK : 8 ≤ stechK := eight_le_stechK
    have hLamK : Real.log (Work.BMF.pC + 8) / Real.log 2 + 4 ≤ stechK := by
      linarith only [stechK_ge_exp_bound]
    have hLam1K : Real.log (Work.BMF.pC + 8) / Real.log 2 + 4 + 1 ≤ stechK := by
      linarith only [stechK_ge_exp_bound]
    have hkr : 0 ≤ 2 * (k : ℝ) * (r : ℝ) := by positivity
    have hk2n : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    have hA1 : 2 * (k : ℝ) * (r : ℝ) * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4)
          + 2 * (k : ℝ) * (r : ℝ) ≤ stechK * (2 * (k : ℝ) * (r : ℝ)) := by
      have he : 2 * (k : ℝ) * (r : ℝ) * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4)
          + 2 * (k : ℝ) * (r : ℝ)
          = 2 * (k : ℝ) * (r : ℝ) * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4 + 1) := by ring
      rw [he]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hLam1K hkr
    have hA2 : (k : ℝ) ^ 2 * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4)
        ≤ stechK * (k : ℝ) ^ 2 := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hLamK hk2n
    have hA3 : (k : ℝ) + 6 ≤ stechK * (k : ℝ) := by nlinarith only [hK, hk2]
    have hexp : stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1))
        = stechK * (2 * (k : ℝ) * (r : ℝ)) + stechK * (k : ℝ) ^ 2 + stechK * (k : ℝ) := by ring
    rw [hexp]
    nlinarith only [hA1, hA2, hA3]
  have hstepC : 7 + (k : ℝ) * Real.log (k : ℝ) + 6 * Real.log (k : ℝ)
        + (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
          * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) * Real.log (k : ℝ)
        + 2 * (k : ℝ) * (r : ℝ) * Real.log (k : ℝ)
      ≤ stechK * (k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) * (1 + Real.log (k : ℝ)) := by
    have hK : 8 ≤ stechK := eight_le_stechK
    have h7 : 7 ≤ stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1)) := by
      have hk5 : 5 ≤ (k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) := by nlinarith only [hk2, hr1]
      nlinarith only [hK, hk5]
    have hcoef : (k : ℝ) + 6 + (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) ^ 2)
          * (Real.log (Work.BMF.pC + 8) / Real.log 2 + 4) + 2 * (k : ℝ) * (r : ℝ)
        ≤ stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1)) := hlin
    have hmul := mul_le_mul_of_nonneg_right hcoef hL0
    have hexp2 : stechK * (k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) * (1 + Real.log (k : ℝ))
        = stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1))
          + stechK * ((k : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1)) * Real.log (k : ℝ) := by ring
    rw [hexp2]
    nlinarith only [h7, hmul, hL0]
  exact le_trans hstepA (le_trans hstepB hstepC)

end Work.BMF.liouville
