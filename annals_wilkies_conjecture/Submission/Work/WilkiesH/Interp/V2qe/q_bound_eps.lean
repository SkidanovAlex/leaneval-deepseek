import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.V2Q.log_QV_le
import Submission.Work.WilkiesH.Interp.V2dV.dV_upper
import Submission.Work.WilkiesH.Interp.V2qb.Qval
import Submission.Work.WilkiesH.Interp.V2qb.q_bound_b_succ
import Submission.Work.WilkiesH.Interp.V2qe._aux
import Submission.Work.WilkiesH.Interp.V2qe.Budget

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qe

open Work.WilkiesH.Interp V2qb

/-! ## Expanding `log (1 / epsV)` -/

lemma log_numV_le (μ g H : ℕ) :
    Real.log (4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
        ((dV μ g (bV μ g H) : ℕ) : ℝ) * ((μ:ℝ)+1))
      ≤ 4 + (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) + ((μ:ℝ)+1)
        + Real.log ((N1V μ g H : ℕ) : ℝ) + Real.log ((QV μ g H : ℕ) : ℝ) := by
  have hN : (0:ℝ) < ((N1V μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H)
  have hQ : (0:ℝ) < ((QV μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H)
  have hD : (0:ℝ) < ((dV μ g (bV μ g H) : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_dV μ g (bV μ g H))
  have hm : (0:ℝ) < (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
  have h4p : (0:ℝ) < 4 := by norm_num
  have hNQ : (0:ℝ) < 4 * ((N1V μ g H : ℕ) : ℝ) := mul_pos h4p hN
  have hNQD : (0:ℝ) < 4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) := mul_pos hNQ hQ
  have hNQDd : (0:ℝ) < 4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
      ((dV μ g (bV μ g H) : ℕ) : ℝ) := mul_pos hNQD hD
  have hlog : Real.log (4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
        ((dV μ g (bV μ g H) : ℕ) : ℝ) * ((μ:ℝ)+1))
      = Real.log 4 + Real.log ((N1V μ g H : ℕ) : ℝ) + Real.log ((QV μ g H : ℕ) : ℝ)
        + Real.log ((dV μ g (bV μ g H) : ℕ) : ℝ) + Real.log ((μ:ℝ)+1) := by
    rw [Real.log_mul (ne_of_gt hNQDd) (ne_of_gt hm),
        Real.log_mul (ne_of_gt hNQD) (ne_of_gt hD),
        Real.log_mul (ne_of_gt hNQ) (ne_of_gt hQ),
        Real.log_mul (ne_of_gt h4p) (ne_of_gt hN)]
  rw [hlog]
  have h4 : Real.log 4 ≤ (4:ℝ) := Real.log_le_self (by norm_num)
  have hd : Real.log ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤ ((dV μ g (bV μ g H) : ℕ) : ℝ) + 1 :=
    log_nat_le_succ _
  have hmu : Real.log ((μ:ℝ)+1) ≤ (μ:ℝ)+1 := Real.log_le_self (le_of_lt hm)
  linarith [h4, hd, hmu]

lemma log_innerV (μ g H : ℕ) (hH : 1 ≤ H) :
    Real.log (((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
        ((H:ℝ) ^ (((μ+1)+1) * dV μ g (bV μ g H) * g)))
      = Real.log ((N1V μ g H : ℕ) : ℝ) + Real.log ((QV μ g H : ℕ) : ℝ)
        + (((((μ+1)+1) * dV μ g (bV μ g H) * g : ℕ) : ℝ) * Real.log (H:ℝ)) := by
  have hN : (0:ℝ) < ((N1V μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H)
  have hQ : (0:ℝ) < ((QV μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H)
  have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  have hpow : (0:ℝ) < (H:ℝ) ^ (((μ+1)+1) * dV μ g (bV μ g H) * g) :=
    lt_of_lt_of_le zero_lt_one (one_le_pow₀ hH1)
  have hNQ : (0:ℝ) < ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) := mul_pos hN hQ
  rw [Real.log_mul (ne_of_gt hNQ) (ne_of_gt hpow),
      Real.log_mul (ne_of_gt hN) (ne_of_gt hQ), Real.log_pow]

lemma log_epsV_le_sum (μ g H : ℕ) (hH : 1 ≤ H) (hlam : 1 ≤ lamV μ g H) :
    Real.log (1 / epsV μ g H) ≤
      (4 + (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) + ((μ:ℝ)+1))
      + (2 * (1 + (g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)))
      + (16 * (1 + (g:ℝ)))
      + ((1 + (g:ℝ)) * ((bV μ g H : ℕ):ℝ) * Real.log ((KK μ : ℕ):ℝ))
      + (((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ)) := by
  rw [log_one_div_epsV_aux μ g H hH]
  set N : ℝ := ((N1V μ g H : ℕ) : ℝ) with hN
  set Q : ℝ := ((QV μ g H : ℕ) : ℝ) with hQ
  set dd : ℝ := ((dV μ g (bV μ g H) : ℕ) : ℝ) with hdd
  set b : ℝ := ((bV μ g H : ℕ) : ℝ) with hb
  set K : ℝ := ((KK μ : ℕ) : ℝ) with hK
  set m : ℝ := ((μ : ℕ) : ℝ) with hm
  set gr : ℝ := ((g : ℕ) : ℝ) with hgr
  set Hr : ℝ := ((H : ℕ) : ℝ) with hHr
  set E : ℕ := (((μ + 1) + 1) * dV μ g (bV μ g H) * g) with hE
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H))
  have hQpos : 0 < Q := by
    rw [hQ]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H))
  have hddpos : 0 < dd := by
    rw [hdd]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_dV μ g (bV μ g H)))
  have hHr1 : 1 ≤ Hr := by rw [hHr]; exact_mod_cast hH
  have hgr0 : 0 ≤ gr := by rw [hgr]; exact Nat.cast_nonneg _
  have hm0 : 0 ≤ m := by rw [hm]; exact Nat.cast_nonneg _
  have hm1 : 0 < m + 1 := by linarith
  have hNQp : 0 < N*Q := mul_pos hNpos hQpos
  have h4N : 0 < 4*N := mul_pos (by norm_num) hNpos
  have h4NQ : 0 < 4*N*Q := mul_pos h4N hQpos
  have h4NQdd : 0 < 4*N*Q*dd := mul_pos h4NQ hddpos
  have hHpow : 0 < Hr^E := lt_of_lt_of_le zero_lt_one (one_le_pow₀ hHr1)
  have hlogN : Real.log N ≤ (m+1)*(dd+1) := by
    rw [hN, hm, hdd]; exact log_N1V_le μ g H
  have hlogQ : Real.log Q ≤ Real.log 16 + Real.log N + b * Real.log K := by
    rw [hQ, hN, hb, hK]; exact V2Q.log_QV_le μ g H hlam
  have hlog16 : Real.log 16 ≤ (16:ℝ) := Real.log_le_self (by norm_num)
  have hlog4 : Real.log 4 ≤ (4:ℝ) := Real.log_le_self (by norm_num)
  have hlogd : Real.log dd ≤ dd + 1 := by rw [hdd]; exact log_nat_le_succ _
  have hlogm : Real.log (m+1) ≤ m + 1 := Real.log_le_self (le_of_lt hm1)
  have hlog1 : Real.log (4*N*Q*dd*(m+1))
      = Real.log 4 + Real.log N + Real.log Q + Real.log dd + Real.log (m+1) := by
    rw [Real.log_mul (ne_of_gt h4NQdd) (ne_of_gt hm1),
        Real.log_mul (ne_of_gt h4NQ) (ne_of_gt hddpos),
        Real.log_mul (ne_of_gt h4N) (ne_of_gt hQpos),
        Real.log_mul (ne_of_gt (by norm_num : (0:ℝ) < 4)) (ne_of_gt hNpos)]
  have hlog2 : Real.log (N*Q*Hr^E) = Real.log N + Real.log Q + (E:ℝ) * Real.log Hr := by
    rw [Real.log_mul (ne_of_gt hNQp) (ne_of_gt hHpow),
        Real.log_mul (ne_of_gt hNpos) (ne_of_gt hQpos), Real.log_pow]
  have hEgr : (E:ℝ) * gr = (m+2)*dd*gr^2 := by
    rw [hE, hm, hdd, hgr]; push_cast; ring
  have hpart1 : Real.log (4*N*Q*dd*(m+1)) ≤ 4 + (dd+1) + (m+1) + Real.log N + Real.log Q := by
    rw [hlog1]; linarith [hlog4, hlogd, hlogm]
  have hpart2 : gr * Real.log (N*Q*Hr^E)
      = gr*(Real.log N + Real.log Q) + (m+2)*dd*gr^2*Real.log Hr := by
    rw [hlog2]
    have h1 : gr * (Real.log N + Real.log Q + (E:ℝ) * Real.log Hr)
        = gr * (Real.log N + Real.log Q) + ((E:ℝ)*gr) * Real.log Hr := by ring
    rw [h1, hEgr]
  have hmain1 : Real.log (4*N*Q*dd*(m+1)) + gr * Real.log (N*Q*Hr^E)
      ≤ (4 + (dd+1) + (m+1)) + (1+gr) * (Real.log N + Real.log Q)
          + (m+2)*dd*gr^2*Real.log Hr := by
    rw [hpart2]
    have he : (1+gr) * (Real.log N + Real.log Q)
        = (Real.log N + Real.log Q) + gr * (Real.log N + Real.log Q) := by ring
    rw [he]
    linarith [hpart1]
  have hmain2 : (4 + (dd+1) + (m+1)) + (1+gr) * (Real.log N + Real.log Q)
        + (m+2)*dd*gr^2*Real.log Hr
      ≤ (4 + (dd+1) + (m+1)) + (2 * (1+gr) * ((m+1)*(dd+1))) + (16*(1+gr))
          + ((1+gr)*b*Real.log K) + ((m+2)*dd*gr^2*Real.log Hr) := by
    have hQ1 : Real.log N + Real.log Q ≤ 2 * Real.log N + 16 + b * Real.log K := by
      linarith [hlogQ, hlog16]
    have hQ2 : 2 * Real.log N + 16 + b * Real.log K ≤ 2 * ((m+1)*(dd+1)) + 16 + b * Real.log K := by
      linarith [hlogN]
    have hstep : (1+gr) * (Real.log N + Real.log Q)
        ≤ (1+gr) * (2*((m+1)*(dd+1)) + 16 + b*Real.log K) :=
      mul_le_mul_of_nonneg_left (le_trans hQ1 hQ2) (by linarith)
    have hExp : (1+gr) * (2*((m+1)*(dd+1)) + 16 + b*Real.log K)
        = 2 * (1+gr) * ((m+1)*(dd+1)) + 16*(1+gr) + (1+gr)*b*Real.log K := by ring
    rw [hExp] at hstep
    linarith [hstep]
  linarith [hmain1, hmain2]

-- `log (1/ε) ≤ q`, where `ε = liou μ d Q g H / (4 N₁ Q d (μ+1))` and
-- `qPoly` evaluates to `CCc μ (1+D) (1+g)^(Ec μ) (1+log H)^(Fc μ)`.
-- Explicitly, `log (1/ε) = log (1/liou) + log (4 N₁ Q d (μ+1))` with
-- `log (1/liou) = g (log N₁ + log Q) + (μ+2) d g² log H` and
-- `log Q ≤ log 16 + log N₁ + bV log (KK μ)` (this is `V2Q.log_QV_le`, using `hlam : 1 ≤ lamV`);
-- the dominant terms are `g · bV log K / λ` and `(μ+2) d g² log H`, both bounded by explicit
-- powers of `(1+g)` and `(1+log H)`, using `d ≤ 8 ((μ+1)!(8g+9))^(1/(μ+1)) (bV+2)^(μ/(μ+1))`
-- and `bV ≤ EE μ (g+1)^A Lg^B` with `Lg = lgNat H ≤ log H + 2`.
theorem q_bound_eps (μ D g H : ℕ) (hH : 1 ≤ H) (hlam : 1 ≤ Work.WilkiesH.Interp.lamV μ g H)
    (hd : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    Real.log (1 / Work.WilkiesH.Interp.epsV μ g H) ≤
      MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] (Work.WilkiesH.Interp.qPoly μ) := by
  rw [qval_eq_eval]
  have hb1 := q_bound_b_succ μ D g H hH
  rw [qval_eq_eval] at hb1
  have hb2 : ((bV μ g H : ℕ) : ℝ) ≤ qval μ D g H := by linarith
  have hdM := dV_le_qval_rpow_aux μ D g H hH hb2 hd
  have hsum := log_epsV_le_sum μ g H hH hlam
  have hA := budget_A μ D g H hH hdM
  have hB := budget_B μ D g H hH hdM
  have hC := budget_C μ D g H hH
  have hD := budget_D μ D g H hH
  have hE := budget_E μ D g H hH hdM
  linarith [hsum, hA, hB, hC, hD, hE]

end Work.WilkiesH.Interp.V2qe
