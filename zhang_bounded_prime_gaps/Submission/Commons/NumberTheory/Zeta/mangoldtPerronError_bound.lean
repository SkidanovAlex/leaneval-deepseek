import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.Analysis.ExpLog.log_nat_add_rpow_div_summable_bound
import Submission.Commons.NumberTheory.Zeta.middle_min_dist_sum_le

open scoped BigOperators
open Finset

noncomputable section

namespace Commons.NumberTheory.Zeta

/-! The two supporting estimates, re-exposed privately for readability. -/

private theorem logBoundLoc :
    ∀ u : ℝ, 0 < u → u ≤ 1 →
      Summable (fun n : ℕ => Real.log (n + 1) / ((n + 1 : ℝ) ^ (1 + u))) ∧
      (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ (1 + u))) ≤ 100 / u ^ 2 :=
  Commons.Analysis.ExpLog.log_nat_add_rpow_div_summable_bound

private theorem middleBoundLoc (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) :
    (∑ n ∈ Finset.Icc (Nat.floor (x / 2) + 1) (Nat.floor (2 * x)),
        min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))) ≤
      100 * (x * Real.log x / T) + 100 :=
  Commons.NumberTheory.Zeta.middle_min_dist_sum_le x T hx hT

/-! ## Basic objects -/

private def lam (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)

private def kern (x T : ℝ) (n : ℕ) : ℝ :=
  min (1 : ℝ) (1 / (T * |Real.log (x / (n : ℝ))|))

private def rp (x : ℝ) (n : ℕ) : ℝ := (x / (n : ℝ)) ^ (1 + 1 / Real.log x)

private def tt (x T : ℝ) (n : ℕ) : ℝ := lam n * rp x n * kern x T n

private def d1s (u : ℝ) (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + u))

private def qn (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ) * (x / (n + 1 : ℝ)) ^ (1 + 1 / Real.log x)

/-! ## Context lemmas (x ≥ 3) -/

private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  have h : Real.exp (1 : ℝ) < (3 : ℝ) := Real.exp_one_lt_three
  have hlog : Real.log (Real.exp (1 : ℝ)) < Real.log (3 : ℝ) :=
    Real.log_lt_log (Real.exp_pos (1 : ℝ)) h
  simpa using hlog

private lemma logx_ge_one {x : ℝ} (hx : 3 ≤ x) : (1 : ℝ) ≤ Real.log x := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hle : Real.log (3 : ℝ) ≤ Real.log x := Real.log_le_log h3 hx
  have h1 : (1 : ℝ) < Real.log (3 : ℝ) := log_three_gt_one
  linarith

private lemma logx_pos {x : ℝ} (hx : 3 ≤ x) : (0 : ℝ) < Real.log x := by
  have := logx_ge_one hx; linarith

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h
  linarith

private lemma inv_log_two_le_two : (1 / Real.log 2 : ℝ) ≤ 2 := by
  have h : 0 < Real.log 2 := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) half_le_log_two
  rw [div_le_iff₀ h]
  nlinarith [half_le_log_two]

private lemma log_two_le_one : Real.log 2 ≤ (1 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h
  linarith

private lemma log_two_mul {x : ℝ} (hx : 0 < x) : Real.log (2 * x) = Real.log 2 + Real.log x := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Real.log_mul h2 hx0]

private lemma log_two_mul_le_two_log {x : ℝ} (hx : 3 ≤ x) : Real.log (2 * x) ≤ 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  calc
    Real.log (2 * x) = Real.log 2 + Real.log x := log_two_mul hx0
    _ ≤ 1 + Real.log x := by linarith [log_two_le_one]
    _ ≤ 2 * Real.log x := by linarith [logx_ge_one hx]

private lemma u_pos {x : ℝ} (hx : 3 ≤ x) : 0 < 1 / Real.log x := by
  exact one_div_pos.mpr (logx_pos hx)

private lemma u_le_one {x : ℝ} (hx : 3 ≤ x) : 1 / Real.log x ≤ 1 := by
  rw [div_le_iff₀ (logx_pos hx)]
  nlinarith [logx_ge_one hx]

private lemma c_le_two {x : ℝ} (hx : 3 ≤ x) : 1 + 1 / Real.log x ≤ 2 := by
  linarith [u_le_one hx]

private lemma c_pos {x : ℝ} (hx : 3 ≤ x) : 0 < 1 + 1 / Real.log x := by
  have h : 0 < 1 / Real.log x := u_pos hx
  linarith

private lemma c_one_le {x : ℝ} (hx : 3 ≤ x) : (1 : ℝ) ≤ 1 + 1 / Real.log x := by
  linarith [u_pos hx]

private lemma x_rpow_inv_log_le_three {x : ℝ} (hx : 3 ≤ x) : x ^ (1 / Real.log x) ≤ 3 := by
  have hx0 : 0 < x := by linarith
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt (logx_pos hx)
  have hE : x ^ (1 / Real.log x) = Real.exp (1 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    field_simp [hlog_ne]
  rw [hE]
  exact le_of_lt Real.exp_one_lt_three

private lemma x_rpow_c_le_three_mul {x : ℝ} (hx : 3 ≤ x) : x ^ (1 + 1 / Real.log x) ≤ 3 * x := by
  have hx0 : 0 < x := by linarith
  calc
    x ^ (1 + 1 / Real.log x) = x ^ (1 : ℝ) * x ^ (1 / Real.log x) := by
      rw [Real.rpow_add hx0]
    _ = x * x ^ (1 / Real.log x) := by rw [Real.rpow_one]
    _ ≤ x * 3 := by
      exact mul_le_mul_of_nonneg_left (x_rpow_inv_log_le_three hx) (by linarith)
    _ = 3 * x := by ring

/-! ## qn = x^c · d1s and the series bounds -/

private lemma qn_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    qn x n = x ^ (1 + 1 / Real.log x) * d1s (1 / Real.log x) n := by
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  have hnpn : 0 ≤ (n : ℝ) + 1 := le_of_lt hnp
  have hdiv : (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) =
        x ^ (1 + 1 / Real.log x) / ((n : ℝ) + 1) ^ (1 + 1 / Real.log x) :=
    Real.div_rpow hx hnpn (1 + 1 / Real.log x)
  unfold qn d1s
  rw [hdiv]
  field_simp [ne_of_gt hnp]

private lemma d1s_summable_bound {x : ℝ} (hx : 3 ≤ x) :
    Summable (d1s (1 / Real.log x)) ∧
      (∑' n : ℕ, d1s (1 / Real.log x) n) ≤ 100 * (Real.log x) ^ 2 := by
  have h := logBoundLoc (1 / Real.log x) (u_pos hx) (u_le_one hx)
  constructor
  · refine Summable.congr h.1 ?_
    intro n
    unfold d1s
    rfl
  · have hE : (∑' n : ℕ, d1s (1 / Real.log x) n) =
        (∑' n : ℕ, Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + 1 / Real.log x))) := by
      apply tsum_congr
      intro n
      unfold d1s
      rfl
    rw [hE]
    calc
      (∑' n : ℕ, Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + 1 / Real.log x)))
          ≤ 100 / (1 / Real.log x) ^ 2 := h.2
      _ = 100 * (Real.log x) ^ 2 := by
        have hL : (Real.log x) ≠ 0 := ne_of_gt (logx_pos hx)
        field_simp [hL]

private lemma qn_summable {x : ℝ} (hx : 3 ≤ x) : Summable (qn x) := by
  have hD := d1s_summable_bound hx
  have hscaled : Summable (fun n : ℕ => x ^ (1 + 1 / Real.log x) * d1s (1 / Real.log x) n) :=
    Summable.mul_left (x ^ (1 + 1 / Real.log x)) hD.1
  exact Summable.congr hscaled (fun n => (qn_eq (by linarith : 0 ≤ x) n).symm)

private lemma qn_tsum_le {x : ℝ} (hx : 3 ≤ x) :
    (∑' n : ℕ, qn x n) ≤ 300 * x * (Real.log x) ^ 2 := by
  have hD := d1s_summable_bound hx
  have hx0 : 0 ≤ x := by linarith
  calc
    (∑' n : ℕ, qn x n) = ∑' n : ℕ, x ^ (1 + 1 / Real.log x) * d1s (1 / Real.log x) n := by
      apply tsum_congr
      intro n
      exact qn_eq hx0 n
    _ = x ^ (1 + 1 / Real.log x) * (∑' n : ℕ, d1s (1 / Real.log x) n) := by
      rw [tsum_mul_left]
    _ ≤ x ^ (1 + 1 / Real.log x) * (100 * (Real.log x) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hD.2 (Real.rpow_nonneg (by linarith : 0 ≤ x) _)
    _ ≤ (3 * x) * (100 * (Real.log x) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (x_rpow_c_le_three_mul hx) (by positivity)
    _ = 300 * x * (Real.log x) ^ 2 := by ring

private lemma d1s_nonneg (u : ℝ) (hu : 0 < u) (n : ℕ) : 0 ≤ d1s u n := by
  unfold d1s
  have h1 : 1 ≤ (n + 1 : ℝ) := by
    have h0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hlog : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg h1
  have hpow : 0 < (n + 1 : ℝ) ^ (1 + u) := Real.rpow_pos_of_pos (by linarith) (1 + u)
  positivity

private lemma qn_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ qn x n := by
  unfold qn
  have h1 : 1 ≤ (n + 1 : ℝ) := by
    have h0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hlog : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg h1
  have hpow : 0 ≤ (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) :=
    Real.rpow_nonneg (div_nonneg hx (by positivity)) (1 + 1 / Real.log x)
  nlinarith


/-! ## Pointwise facts -/

private lemma lam_nonneg (n : ℕ) : 0 ≤ lam n := by
  exact ArithmeticFunction.vonMangoldt_nonneg (n := n)

private lemma lam_le_log (n : ℕ) : lam n ≤ Real.log (n : ℝ) := by
  simpa [lam] using (ArithmeticFunction.vonMangoldt_le_log (n := n))

private lemma log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  exact Real.log_natCast_nonneg n

private lemma log_add_one_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 1) := by
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have h1 : 1 ≤ (n : ℝ) + 1 := by nlinarith
  exact Real.log_nonneg h1

private lemma log_add_one_le (n : ℕ) : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
    exact Real.log_le_log hn0 hle

private lemma rp_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ rp x n := by
  unfold rp
  have hb : 0 ≤ x / (n : ℝ) := div_nonneg hx (by positivity)
  exact Real.rpow_nonneg hb (1 + 1 / Real.log x)

private lemma kern_le_one (x T : ℝ) (n : ℕ) : kern x T n ≤ 1 := by
  unfold kern
  exact min_le_left _ _

private lemma kern_nonneg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) (n : ℕ) : 0 ≤ kern x T n := by
  unfold kern
  have hy : 0 ≤ 1 / (T * |Real.log (x / (n : ℝ))|) := by
    have hTl : 0 ≤ T * |Real.log (x / (n : ℝ))| := mul_nonneg hT (abs_nonneg _)
    exact one_div_nonneg.mpr hTl
  exact le_min (by norm_num) hy

private lemma tt_nonneg {x T : ℝ} (hT : 0 ≤ T) (hx0 : 0 ≤ x) (n : ℕ) : 0 ≤ tt x T n := by
  unfold tt
  exact mul_nonneg (mul_nonneg (lam_nonneg n) (rp_nonneg hx0 n)) (kern_nonneg hT x n)

private lemma rp_le_four_pb {x : ℝ} (hx : 3 ≤ x) (n : ℕ) :
    rp x n ≤ 4 * (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  by_cases hn : n = 0
  · subst n
    unfold rp
    have hz : (x / ((0 : ℕ) : ℝ)) ^ (1 + 1 / Real.log x) = 0 := by
      have hq : x / ((0 : ℕ) : ℝ) = 0 := by simp
      rw [hq]
      exact Real.zero_rpow (ne_of_gt (c_pos hx))
    rw [hz]
    have hd : 0 < (((0 : ℕ) : ℝ) + 1) := by norm_num
    have hp : 0 ≤ (x / (((0 : ℕ) : ℝ) + 1)) ^ (1 + 1 / Real.log x) :=
      Real.rpow_nonneg (div_nonneg hx0 hd.le) _
    nlinarith
  · have hn1 : (1 : ℕ) ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn)
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hn0le : 0 ≤ (n : ℝ) := le_of_lt hn0
    have hposn1 : 0 < (n : ℝ) + 1 := by nlinarith
    have hc0 : 0 ≤ 1 + 1 / Real.log x := by
      have h : 0 < 1 / Real.log x := u_pos hx
      nlinarith
    have hc2 : 1 + 1 / Real.log x ≤ 2 := c_le_two hx
    have hbase : x / (n : ℝ) ≤ 2 * (x / ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hn0, ne_of_gt hposn1]
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hm : x ≤ x * (n : ℝ) := by
        simpa using (mul_le_mul_of_nonneg_left hn1' hx0)
      nlinarith
    have hmono1 : (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤
        (2 * (x / ((n : ℝ) + 1))) ^ (1 + 1 / Real.log x) := by
      exact Real.rpow_le_rpow (div_nonneg hx0 hn0le) hbase hc0
    have hsplit : (2 * (x / ((n : ℝ) + 1))) ^ (1 + 1 / Real.log x) =
        (2 : ℝ) ^ (1 + 1 / Real.log x) * (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) := by
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hx0 hposn1.le)
    have h2 : (2 : ℝ) ^ (1 + 1 / Real.log x) ≤ 4 := by
      have h2c : (2 : ℝ) ^ (1 + 1 / Real.log x) ≤ (2 : ℝ) ^ (2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc2
      have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
      nlinarith
    calc
      (x / (n : ℝ)) ^ (1 + 1 / Real.log x)
          ≤ (2 * (x / ((n : ℝ) + 1))) ^ (1 + 1 / Real.log x) := hmono1
      _ = (2 : ℝ) ^ (1 + 1 / Real.log x) * (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) := hsplit
      _ ≤ 4 * (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x) := by
        exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (div_nonneg hx0 hposn1.le) _)

private lemma lam_rp_le_four_qn {x : ℝ} (hx : 3 ≤ x) (n : ℕ) : lam n * rp x n ≤ 4 * qn x n := by
  calc
    lam n * rp x n ≤ Real.log (n : ℝ) * rp x n := by
      exact mul_le_mul_of_nonneg_right (lam_le_log n) (rp_nonneg (by linarith : 0 ≤ x) n)
    _ ≤ Real.log ((n : ℝ) + 1) * rp x n := by
      exact mul_le_mul_of_nonneg_right (log_add_one_le n) (rp_nonneg (by linarith : 0 ≤ x) n)
    _ ≤ Real.log ((n : ℝ) + 1) * (4 * (x / ((n : ℝ) + 1)) ^ (1 + 1 / Real.log x)) := by
      exact mul_le_mul_of_nonneg_left (rp_le_four_pb hx n) (log_add_one_nonneg n)
    _ = 4 * qn x n := by
      unfold qn
      ring

private lemma tt_le_four_qn {x T : ℝ} (hx : 3 ≤ x) (n : ℕ) : tt x T n ≤ 4 * qn x n := by
  calc
    tt x T n = lam n * rp x n * kern x T n := rfl
    _ ≤ lam n * rp x n * 1 := by
      exact mul_le_mul_of_nonneg_left (kern_le_one x T n) (mul_nonneg (lam_nonneg n) (rp_nonneg (by linarith : 0 ≤ x) n))
    _ = lam n * rp x n := by ring
    _ ≤ 4 * qn x n := lam_rp_le_four_qn hx n

private lemma kern_le_two_div_T {x T : ℝ} (hT : 0 < T) (n : ℕ)
    (hlog : Real.log 2 ≤ |Real.log (x / (n : ℝ))|) : kern x T n ≤ 2 / T := by
  unfold kern
  have hl0 : 0 < Real.log 2 := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) half_le_log_two
  have hTl : 0 < T * Real.log 2 := mul_pos hT hl0
  have hTl' : T * Real.log 2 ≤ T * |Real.log (x / (n : ℝ))| := by
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt hT)
  have h1 : 1 / (T * |Real.log (x / (n : ℝ))|) ≤ 1 / (T * Real.log 2) := by
    exact one_div_le_one_div_of_le hTl hTl'
  have h2 : min (1 : ℝ) (1 / (T * |Real.log (x / (n : ℝ))|)) ≤ 1 / (T * Real.log 2) := by
    exact le_trans (min_le_right _ _) h1
  have h3 : 1 / (T * Real.log 2) ≤ 2 / T := by
    field_simp [hT.ne', ne_of_gt hl0]
    have hm : (1 : ℝ) ≤ 2 * Real.log 2 := by nlinarith [half_le_log_two]
    have hm2 : T ≤ 2 * T * Real.log 2 := by
      calc
        T = T * 1 := by ring
        _ ≤ T * (2 * Real.log 2) := mul_le_mul_of_nonneg_left hm hT.le
        _ = 2 * T * Real.log 2 := by ring
    nlinarith
  exact le_trans h2 h3

private lemma tt_le_frac_T_mul_qn {x T : ℝ} (hx : 3 ≤ x) (hT : 2 ≤ T) (n : ℕ)
    (hlog : Real.log 2 ≤ |Real.log (x / (n : ℝ))|) : tt x T n ≤ (8 / T) * qn x n := by
  have hTpos : 0 < T := by linarith
  have hk : kern x T n ≤ 2 / T := kern_le_two_div_T hTpos n hlog
  have hA : 0 ≤ lam n * rp x n := mul_nonneg (lam_nonneg n) (rp_nonneg (by linarith : 0 ≤ x) n)
  calc
    tt x T n = (lam n * rp x n) * kern x T n := by rfl
    _ ≤ (lam n * rp x n) * (2 / T) := by
      exact mul_le_mul_of_nonneg_left hk hA
    _ = (2 / T) * (lam n * rp x n) := by ring
    _ ≤ (2 / T) * (4 * qn x n) := by
      exact mul_le_mul_of_nonneg_left (lam_rp_le_four_qn hx n) (by positivity)
    _ = (8 / T) * qn x n := by ring


/-! ## Floor/range facts -/

private lemma floor_half_le {x : ℝ} (hx : 0 ≤ x) :
    ((Nat.floor (x / 2) : ℕ) : ℝ) ≤ x / 2 := by
  exact Nat.floor_le (div_nonneg hx (by norm_num))

private lemma lt_floor_half_add_one (x : ℝ) :
    x / 2 < ((Nat.floor (x / 2) : ℕ) : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (x / 2)

private lemma floor_two_mul_le {x : ℝ} (hx : 0 ≤ x) :
    ((Nat.floor (2 * x) : ℕ) : ℝ) ≤ 2 * x := by
  exact Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx)

private lemma lt_floor_two_mul_add_one (x : ℝ) :
    2 * x < ((Nat.floor (2 * x) : ℕ) : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (2 * x)

private lemma of_floor_half_le {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≤ Nat.floor (x / 2)) :
    (n : ℝ) ≤ x / 2 := by
  exact le_trans (by exact_mod_cast hn) (floor_half_le hx)

private lemma of_floor_two_mul_add_one_lt {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : Nat.floor (2 * x) + 1 ≤ n) : 2 * x < (n : ℝ) := by
  have h1 : 2 * x < ((Nat.floor (2 * x) : ℕ) : ℝ) + 1 := lt_floor_two_mul_add_one x
  have h2 : ((Nat.floor (2 * x) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  exact lt_of_lt_of_le h1 h2

private lemma of_mid_mem_half_lt {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : Nat.floor (x / 2) + 1 ≤ n) : x / 2 < (n : ℝ) := by
  have h1 : x / 2 < ((Nat.floor (x / 2) : ℕ) : ℝ) + 1 := lt_floor_half_add_one x
  have h2 : ((Nat.floor (x / 2) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  exact lt_of_lt_of_le h1 h2

private lemma of_mid_mem_two_mul_le {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : n ≤ Nat.floor (2 * x)) : (n : ℝ) ≤ 2 * x := by
  exact le_trans (by exact_mod_cast hn) (floor_two_mul_le hx)

/-! ## log lower bounds -/

private lemma log_ge_one_sub_inv {t : ℝ} (ht : 0 < t) : 1 - t⁻¹ ≤ Real.log t := by
  have hlog := Real.log_le_sub_one_of_pos (x := t⁻¹) (by positivity : 0 < t⁻¹)
  rw [Real.log_inv t] at hlog
  linarith

-- n ≤ x: (x−n)/(2x) ≤ log(x/n)
private lemma log_ge_sub_div_two {x n : ℝ} (hx : 0 < x) (hn : 0 < n) (hnx : n ≤ x) :
    (x - n) / (2 * x) ≤ Real.log (x / n) := by
  have ht : 0 < n / x := div_pos hn hx
  have hlogs : Real.log (n / x) ≤ n / x - 1 := Real.log_le_sub_one_of_pos ht
  have hE : Real.log (x / n) = -Real.log (n / x) := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hn0 : n ≠ 0 := ne_of_gt hn
    calc
      Real.log (x / n) = Real.log x - Real.log n := Real.log_div hx0 hn0
      _ = -(Real.log n - Real.log x) := by ring
      _ = -(Real.log (n / x)) := by rw [Real.log_div hn0 hx0]
  have hrew : (x - n) / x = 1 - n / x := by
    field_simp [hx.ne']
  have hmain : (x - n) / x ≤ Real.log (x / n) := by
    rw [hE, hrew]
    linarith
  have hsub : 0 ≤ x - n := sub_nonneg.mpr hnx
  have hscale : (x - n) / (2 * x) ≤ (x - n) / x := by
    have h2xn : (2 * x : ℝ) ≠ 0 := by positivity
    field_simp [hx.ne', h2xn]
    nlinarith [hsub]
  exact le_trans hscale hmain

-- x < n ≤ 2x: (n−x)/(2x) ≤ log(n/x)
private lemma log_ge_dist_div_two {x n : ℝ} (hx : 0 < x) (hxn : x < n) (hn2 : n ≤ 2 * x) :
    (n - x) / (2 * x) ≤ Real.log (n / x) := by
  have hn : 0 < n := lt_trans hx hxn
  have ht : 0 < n / x := div_pos hn hx
  have hb : 1 - (n / x)⁻¹ ≤ Real.log (n / x) := log_ge_one_sub_inv ht
  have hrew : 1 - (n / x)⁻¹ = (n - x) / n := by
    field_simp [hx.ne', hn.ne']
  have hmain : (n - x) / n ≤ Real.log (n / x) := by
    rw [← hrew]
    exact hb
  have hsub : 0 ≤ n - x := sub_nonneg.mpr (le_of_lt hxn)
  have hscale : (n - x) / (2 * x) ≤ (n - x) / n := by
    have h2xn : (2 * x : ℝ) ≠ 0 := by positivity
    have hnn : n ≠ 0 := ne_of_gt hn
    field_simp [h2xn, hnn]
    nlinarith [hsub, hn2]
  exact le_trans hscale hmain

/-- For `1 ≤ n ≤ 2x`, `|log (x/n)| ≥ |x − n|/(2x)`. -/
private lemma abs_log_div_ge_dist (x n : ℝ) (hx : 0 < x) (hn1 : 1 ≤ n) (hn2 : n ≤ 2 * x) :
    |Real.log (x / n)| ≥ |x - n| / (2 * x) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn1
  by_cases hle : n ≤ x
  · have hgeom : 1 ≤ x / n := by
      rw [one_le_div₀ hnpos]
      exact hle
    have hlognn : 0 ≤ Real.log (x / n) := Real.log_nonneg hgeom
    rw [abs_of_nonneg hlognn]
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact log_ge_sub_div_two hx hnpos hle
  · have hxn : x < n := lt_of_not_ge hle
    have hgn : 1 ≤ n / x := (one_le_div₀ hx).mpr (le_of_lt hxn)
    have hlognn : 0 ≤ Real.log (n / x) := Real.log_nonneg hgn
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hn0 : n ≠ 0 := ne_of_gt hnpos
    have hE1 : Real.log (x / n) = -Real.log (n / x) := by
      calc
        Real.log (x / n) = Real.log x - Real.log n := Real.log_div hx0 hn0
        _ = -(Real.log n - Real.log x) := by ring
        _ = -(Real.log (n / x)) := by rw [Real.log_div hn0 hx0]
    have habs : |Real.log (x / n)| = Real.log (n / x) := by
      rw [hE1]
      rw [abs_neg]
      exact abs_of_nonneg hlognn
    rw [habs]
    have hxnm : |x - n| = n - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxn))]
      ring
    rw [hxnm]
    exact log_ge_dist_div_two hx hxn hn2


/-! ## far-region |log| ≥ log 2 -/

private lemma log_two_pos : 0 < Real.log 2 := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) half_le_log_two

private lemma abs_log_ge_log_two_of_le_half {x : ℝ} (hx0 : 0 < x) {n : ℕ}
    (hn1 : (1 : ℝ) ≤ (n : ℝ)) (hn : (n : ℝ) ≤ x / 2) :
    Real.log 2 ≤ |Real.log (x / (n : ℝ))| := by
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  have hbig : 2 ≤ x / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    nlinarith
  have hlog : Real.log 2 ≤ Real.log (x / (n : ℝ)) := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hbig
  have hnon : 0 ≤ Real.log (x / (n : ℝ)) := le_trans (le_of_lt log_two_pos) hlog
  rw [abs_of_nonneg hnon]
  exact hlog

private lemma abs_log_ge_log_two_of_two_le {x : ℝ} (hx0 : 0 < x) {n : ℕ}
    (hn : 2 * x ≤ (n : ℝ)) : Real.log 2 ≤ |Real.log (x / (n : ℝ))| := by
  have hnpos : 0 < (n : ℝ) := by
    have h : 0 < 2 * x := by positivity
    exact lt_of_lt_of_le h hn
  have hbig : 2 ≤ (n : ℝ) / x := by
    rw [le_div_iff₀ hx0]
    nlinarith
  have hlog : Real.log 2 ≤ Real.log ((n : ℝ) / x) := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hbig
  have hnon : 0 ≤ Real.log ((n : ℝ) / x) := le_trans (le_of_lt log_two_pos) hlog
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hE : Real.log (x / (n : ℝ)) = -Real.log ((n : ℝ) / x) := by
    calc
      Real.log (x / (n : ℝ)) = Real.log x - Real.log (n : ℝ) := Real.log_div hx0' hn0
      _ = -(Real.log (n : ℝ) - Real.log x) := by ring
      _ = -(Real.log ((n : ℝ) / x)) := by rw [Real.log_div hn0 hx0']
  have habs : |Real.log (x / (n : ℝ))| = Real.log ((n : ℝ) / x) := by
    rw [hE]
    rw [abs_neg]
    exact abs_of_nonneg hnon
  rwa [habs]

/-! ## Middle-region kernel ≤ distance kernel -/

private lemma kern_le_dist_kern {x T : ℝ} {n : ℕ} (hx0 : 0 < x) (hT : 0 < T)
    (hn1 : (1 : ℝ) ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * x) :
    kern x T n ≤ min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
  have hmain := abs_log_div_ge_dist x (n : ℝ) hx0 hn1 hn2
  by_cases hne : x = (n : ℝ)
  · subst hne
    unfold kern
    have hq : (n : ℝ) / (n : ℝ) = 1 := by
      have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
      exact div_self (ne_of_gt hnpos)
    simp [hq]
  · have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
    have hlogpos : 0 < |Real.log (x / (n : ℝ))| := by
      have hd0 : x - (n : ℝ) ≠ 0 := sub_ne_zero.mpr hne
      have hdp : 0 < |x - (n : ℝ)| := abs_pos.mpr hd0
      have hpos2 : 0 < |x - (n : ℝ)| / (2 * x) := div_pos hdp (by positivity)
      exact lt_of_lt_of_le hpos2 hmain
    have hin1 : 1 / (T * |Real.log (x / (n : ℝ))|) ≤ (2 * x) / (T * |x - (n : ℝ)|) := by
      have hd0 : x - (n : ℝ) ≠ 0 := sub_ne_zero.mpr hne
      have hdistpos : 0 < |x - (n : ℝ)| := abs_pos.mpr hd0
      have hTb : 0 < T * |x - (n : ℝ)| := mul_pos hT hdistpos
      have hTa : 0 < T * |Real.log (x / (n : ℝ))| := mul_pos hT hlogpos
      field_simp [hT.ne', ne_of_gt hTa, ne_of_gt hTb]
      have h2x : 0 < 2 * x := by positivity
      have hsc : |x - (n : ℝ)| ≤ |Real.log (x / (n : ℝ))| * (2 * x) := by
        exact (div_le_iff₀ h2x).mp hmain
      have hmul : T * |x - (n : ℝ)| ≤ T * (|Real.log (x / (n : ℝ))| * (2 * x)) :=
        mul_le_mul_of_nonneg_left hsc hT.le
      have hmul2 : T * |x - (n : ℝ)| ≤ (2 * x) * (T * |Real.log (x / (n : ℝ))|) := by
        calc
          T * |x - (n : ℝ)| ≤ T * (|Real.log (x / (n : ℝ))| * (2 * x)) := hmul
          _ = (2 * x) * (T * |Real.log (x / (n : ℝ))|) := by ring
      nlinarith
    have hin2 : min (1 : ℝ) (1 / (T * |Real.log (x / (n : ℝ))|)) ≤
        min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
      exact min_le_min le_rfl hin1
    simpa [kern] using hin2

/-! ## middle-region pointwise bound by 8·log x · dist-kernel -/

private lemma log_nat_le_two_logx {x : ℝ} {n : ℕ} (hx : 3 ≤ x) (hn1 : (1 : ℝ) ≤ (n : ℝ))
    (hn2 : (n : ℝ) ≤ 2 * x) : Real.log (n : ℝ) ≤ 2 * Real.log x := by
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  have hxpos : 0 < x := by linarith
  have h2xpos : 0 < 2 * x := by positivity
  have h1 : Real.log (n : ℝ) ≤ Real.log (2 * x) := Real.log_le_log hnpos hn2
  have h2 : Real.log (2 * x) ≤ 2 * Real.log x := log_two_mul_le_two_log hx
  exact le_trans h1 h2

private lemma rp_le_four_of_gt_half {x : ℝ} {n : ℕ} (hx : 3 ≤ x) (hn : x / 2 < (n : ℝ)) :
    rp x n ≤ 4 := by
  have hnpos : 0 < (n : ℝ) := by
    have h1 : 0 < x / 2 := by linarith
    exact lt_trans h1 hn
  have hbase_ge : 0 ≤ x / (n : ℝ) := div_nonneg (by linarith : 0 ≤ x) hnpos.le
  have hbase : x / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have hc0 : 0 ≤ 1 + 1 / Real.log x := by
    have h : 0 < 1 / Real.log x := u_pos hx
    nlinarith
  have hpow : (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤ (2 : ℝ) ^ (1 + 1 / Real.log x) :=
    Real.rpow_le_rpow hbase_ge hbase hc0
  have h2 : (2 : ℝ) ^ (1 + 1 / Real.log x) ≤ 4 := by
    have h2c : (2 : ℝ) ^ (1 + 1 / Real.log x) ≤ (2 : ℝ) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (c_le_two hx)
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
    nlinarith
  unfold rp
  exact le_trans hpow h2

private lemma lam_rp_le_eight_log_of_mid {x : ℝ} {n : ℕ} (hx : 3 ≤ x) (hn1 : (1 : ℝ) ≤ (n : ℝ))
    (hnlo : x / 2 < (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * x) : lam n * rp x n ≤ 8 * Real.log x := by
  have hL : 0 ≤ Real.log (n : ℝ) := log_natCast_nonneg n
  have hrp : 0 ≤ rp x n := rp_nonneg (by linarith : 0 ≤ x) n
  calc
    lam n * rp x n ≤ Real.log (n : ℝ) * rp x n := by
      exact mul_le_mul_of_nonneg_right (lam_le_log n) hrp
    _ ≤ (2 * Real.log x) * 4 := by
      have hlogle : Real.log (n : ℝ) ≤ 2 * Real.log x := log_nat_le_two_logx hx hn1 hn2
      have hrple : rp x n ≤ 4 := rp_le_four_of_gt_half hx hnlo
      have hnonneg : 0 ≤ 2 * Real.log x := by nlinarith [logx_ge_one hx]
      exact mul_le_mul hlogle hrple hrp hnonneg
    _ = 8 * Real.log x := by ring

private lemma dk_nonneg {x T : ℝ} {n : ℕ} (hx : 0 ≤ x) (hT : 0 ≤ T) :
    0 ≤ min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
  have hnum : 0 ≤ 2 * x := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx
  have hden : 0 ≤ T * |x - (n : ℝ)| := mul_nonneg hT (abs_nonneg _)
  have hy : 0 ≤ (2 * x) / (T * |x - (n : ℝ)|) := div_nonneg hnum hden
  exact le_min (by norm_num) hy

private lemma tt_le_eight_log_dist {x T : ℝ} {n : ℕ} (hx : 3 ≤ x) (hT : 2 ≤ T)
    (hn1 : (1 : ℝ) ≤ (n : ℝ)) (hnlo : x / 2 < (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * x) :
    tt x T n ≤ 8 * Real.log x * min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hdk' : kern x T n ≤ min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) :=
    kern_le_dist_kern hxpos hTpos hn1 hn2
  have hA : 0 ≤ lam n * rp x n := mul_nonneg (lam_nonneg n) (rp_nonneg (by linarith : 0 ≤ x) n)
  have hlr : lam n * rp x n ≤ 8 * Real.log x := lam_rp_le_eight_log_of_mid hx hn1 hnlo hn2
  have hdk : 0 ≤ min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := dk_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ T)
  calc
    tt x T n = (lam n * rp x n) * kern x T n := by rfl
    _ ≤ (lam n * rp x n) * min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
      exact mul_le_mul_of_nonneg_left hdk' hA
    _ ≤ (8 * Real.log x) * min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|)) := by
      exact mul_le_mul_of_nonneg_right hlr hdk

private lemma tt_zero (x T : ℝ) : tt x T 0 = 0 := by
  unfold tt lam kern rp
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg not_isPrimePow_zero]
  ring

private lemma qn_zero (x : ℝ) : qn x 0 = 0 := by
  unfold qn
  norm_num


/-! ## Main bound assembly -/

private def dk (x T : ℝ) (n : ℕ) : ℝ :=
  min (1 : ℝ) ((2 * x) / (T * |x - (n : ℝ)|))

private lemma dk_ge_zero {x T : ℝ} {n : ℕ} (hx : 0 ≤ x) (hT : 0 ≤ T) : 0 ≤ dk x T n := by
  unfold dk
  have hnum : 0 ≤ 2 * x := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx
  have hden : 0 ≤ T * |x - (n : ℝ)| := mul_nonneg hT (abs_nonneg _)
  exact le_min (by norm_num) (div_nonneg hnum hden)

private lemma A_ge_one {x : ℝ} (hx : 3 ≤ x) : (1 : ℕ) ≤ Nat.floor (x / 2) := by
  have h : ((1 : ℕ) : ℝ) ≤ x / 2 := by
    norm_num
    linarith
  exact Nat.le_floor h

private lemma main_bound {x T : ℝ} (hx : 3 ≤ x) (hT : 2 ≤ T) :
    Summable (tt x T) ∧
      (∑' n : ℕ, tt x T n) ≤ 8192 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hL0 : 0 ≤ Real.log x := by linarith [logx_ge_one hx]
  let A : ℕ := Nat.floor (x / 2)
  let B : ℕ := Nat.floor (2 * x)
  have hAB : A ≤ B := by
    have h : x / 2 ≤ 2 * x := by nlinarith
    exact Nat.floor_mono h
  have hqsum : Summable (qn x) := qn_summable hx
  have hqtsum : (∑' n : ℕ, qn x n) ≤ 300 * x * (Real.log x) ^ 2 := qn_tsum_le hx
  have h4q : Summable (fun n : ℕ => 4 * qn x n) := Summable.mul_left (4 : ℝ) hqsum
  have htsum : Summable (tt x T) := Summable.of_nonneg_of_le
      (fun n => tt_nonneg hT0 hx0 n) (fun n => tt_le_four_qn hx n) h4q
  have hqnon : ∀ n : ℕ, 0 ≤ qn x n := fun n => qn_nonneg hx0 n
  let F1 : ℕ → ℝ := fun n => (8 / T) * qn x n
  let F2 : ℕ → ℝ := fun n =>
    if A < n ∧ n ≤ B then 8 * Real.log x * dk x T n else 0
  have hF1 : Summable F1 := Summable.mul_left (8 / T) hqsum
  have hF2 : Summable F2 := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    have hEq : ({n : ℕ | A < n ∧ n ≤ B} : Set ℕ) = (Finset.Icc (A + 1) B : Set ℕ) := by
      ext n
      simp
    have hFin : ({n : ℕ | A < n ∧ n ≤ B} : Set ℕ).Finite := by
      rw [hEq]
      exact (Finset.Icc (A + 1) B).finite_toSet
    have hsub : {n | (if A < n ∧ n ≤ B then 8 * Real.log x * dk x T n else 0) ≠ 0}
        ⊆ ({n : ℕ | A < n ∧ n ≤ B} : Set ℕ) := by
      intro n hn
      change A < n ∧ n ≤ B
      by_contra hbad
      have hzero : (if A < n ∧ n ≤ B then 8 * Real.log x * dk x T n else 0) = 0 := by
        by_cases h : A < n ∧ n ≤ B
        · exact False.elim (hbad h)
        · simp [h]
      exact hn hzero
    exact hFin.subset hsub
  have hF2non : ∀ n : ℕ, 0 ≤ F2 n := by
    intro n
    by_cases h : A < n ∧ n ≤ B
    · simp [F2, h]
      have h8 : 0 ≤ 8 * Real.log x := by nlinarith [hL0]
      exact mul_nonneg h8 (dk_ge_zero hx0 hT0)
    · simp [F2, h]
  -- pointwise tt ≤ F1 + F2
  have hpoint : ∀ n : ℕ, tt x T n ≤ F1 n + F2 n := by
    intro n
    by_cases hm : A < n ∧ n ≤ B
    · have hmem : Nat.floor (x / 2) + 1 ≤ n ∧ n ≤ Nat.floor (2 * x) := by
        simpa [A, B] using hm
      have hn1n : (1 : ℕ) ≤ n := by
        have hA1 : (1 : ℕ) ≤ A := A_ge_one hx
        omega
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1n
      have hnlo : x / 2 < (n : ℝ) := of_mid_mem_half_lt hx0 hmem.1
      have hn2 : (n : ℝ) ≤ 2 * x := of_mid_mem_two_mul_le hx0 hmem.2
      have h1 : tt x T n ≤ 8 * Real.log x * dk x T n := by
        simpa [dk] using (tt_le_eight_log_dist hx hT hn1 hnlo hn2)
      have h2 : 8 * Real.log x * dk x T n = F2 n := by
        simp [F2, hm]
      have h3 : 0 ≤ F1 n := by
        simp [F1]
        exact mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hT0) (hqnon n)
      calc
        tt x T n ≤ 8 * Real.log x * dk x T n := h1
        _ = F2 n := h2
        _ ≤ F1 n + F2 n := by linarith [h3]
    · have hFar : n ≤ A ∨ B < n := by
        by_cases h1 : n ≤ A
        · exact Or.inl h1
        · have hA : A < n := lt_of_not_ge h1
          by_cases h2 : n ≤ B
          · exact False.elim (hm ⟨hA, h2⟩)
          · exact Or.inr (lt_of_not_ge h2)
      have hF2z : F2 n = 0 := by
        have hnot : ¬(A < n ∧ n ≤ B) := by
          intro h
          rcases hFar with h1 | h2
          · have : ¬ A < n := by omega
            exact this h.1
          · have : ¬ n ≤ B := by omega
            exact this h.2
        simp [F2, hnot]
      have hb : tt x T n ≤ F1 n := by
        rcases hFar with h1 | h2
        · by_cases hn0 : n = 0
          · subst n
            have hz1 : tt x T 0 = 0 := tt_zero x T
            have hz2 : qn x 0 = 0 := qn_zero x
            simp [F1, hz1, hz2]
          · have hn1n : (1 : ℕ) ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn0)
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1n
            have hn12 : (n : ℝ) ≤ x / 2 := of_floor_half_le hx0 (by simpa [A] using h1)
            have hlog : Real.log 2 ≤ |Real.log (x / (n : ℝ))| :=
              abs_log_ge_log_two_of_le_half hxpos hn1 hn12
            have ht : tt x T n ≤ (8 / T) * qn x n := tt_le_frac_T_mul_qn hx hT n hlog
            simpa [F1] using ht
        · have hmem : Nat.floor (2 * x) + 1 ≤ n := by simpa [B] using (by omega : B + 1 ≤ n)
          have h2xl : 2 * x < (n : ℝ) := of_floor_two_mul_add_one_lt hx0 hmem
          have hlog : Real.log 2 ≤ |Real.log (x / (n : ℝ))| := abs_log_ge_log_two_of_two_le hxpos (le_of_lt h2xl)
          have ht : tt x T n ≤ (8 / T) * qn x n := tt_le_frac_T_mul_qn hx hT n hlog
          simpa [F1] using ht
      calc
        tt x T n ≤ F1 n := hb
        _ = F1 n + F2 n := by rw [hF2z]; ring
  -- bounds for the pieces
  have hF1sum : (∑' n : ℕ, F1 n) ≤ (8 / T) * (300 * x * (Real.log x) ^ 2) := by
    calc
      (∑' n : ℕ, F1 n) = (8 / T) * (∑' n : ℕ, qn x n) := by
        simp [F1]
        rw [tsum_mul_left]
      _ ≤ (8 / T) * (300 * x * (Real.log x) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hqtsum (by positivity)
  have hF2eq : (∑' n : ℕ, F2 n) = ∑ n ∈ Finset.Icc (A + 1) B, F2 n := by
    exact (tsum_eq_sum (f := F2) (s := Finset.Icc (A + 1) B) (by
      intro n hn
      have hnot : ¬(A < n ∧ n ≤ B) := by
        intro h
        have h1 : A + 1 ≤ n := by omega
        have h2 : n ≤ B := h.2
        exact hn (Finset.mem_Icc.mpr ⟨h1, h2⟩)
      simp [F2, hnot]))
  have hF2sum' : (∑ n ∈ Finset.Icc (A + 1) B, F2 n) ≤
      8 * Real.log x * (100 * (x * Real.log x / T) + 100) := by
    calc
      (∑ n ∈ Finset.Icc (A + 1) B, F2 n)
          = ∑ n ∈ Finset.Icc (A + 1) B, 8 * Real.log x * dk x T n := by
            apply Finset.sum_congr rfl
            intro n hn
            have hmem : A + 1 ≤ n ∧ n ≤ B := Finset.mem_Icc.mp hn
            have hc : A < n ∧ n ≤ B := ⟨by omega, hmem.2⟩
            simp [F2, hc]
      _ = 8 * Real.log x * ∑ n ∈ Finset.Icc (A + 1) B, dk x T n := by
            rw [Finset.mul_sum]
      _ ≤ 8 * Real.log x * (100 * (x * Real.log x / T) + 100) := by
        have hm : (∑ n ∈ Finset.Icc (A + 1) B, dk x T n) ≤ 100 * (x * Real.log x / T) + 100 := by
          simpa [dk, A, B] using middleBoundLoc x T hx hT
        exact mul_le_mul_of_nonneg_left hm (by nlinarith [logx_pos hx])
  have hF2sum : (∑' n : ℕ, F2 n) ≤ 8 * Real.log x * (100 * (x * Real.log x / T) + 100) := by
    rw [hF2eq]
    exact hF2sum'
  -- assemble
  have hdecomp : (∑' n : ℕ, tt x T n) ≤ (∑' n : ℕ, F1 n) + (∑' n : ℕ, F2 n) := by
    have hle : (∑' n : ℕ, tt x T n) ≤ ∑' n : ℕ, (F1 n + F2 n) := by
      exact Summable.tsum_le_tsum hpoint htsum (hF1.add hF2)
    have hsum : (∑' n : ℕ, (F1 n + F2 n)) = (∑' n : ℕ, F1 n) + (∑' n : ℕ, F2 n) := by
      exact hF1.tsum_add hF2
    rwa [hsum] at hle
  have htotal : (∑' n : ℕ, tt x T n) ≤
      (8 / T) * (300 * x * (Real.log x) ^ 2) + 8 * Real.log x * (100 * (x * Real.log x / T) + 100) := by
    exact le_trans hdecomp (add_le_add hF1sum hF2sum)
  constructor
  · exact htsum
  · have h1 : (8 / T) * (300 * x * (Real.log x) ^ 2) ≤ 2400 * (x * (Real.log x) ^ 2 / T) := by
      have hT0 : T ≠ 0 := ne_of_gt hTpos
      field_simp [hT0]
      ring_nf
      nlinarith
    have h2 : 8 * Real.log x * (100 * (x * Real.log x / T) + 100)
        ≤ 800 * (x * (Real.log x) ^ 2 / T) + 800 * Real.log x := by
      have hT0 : T ≠ 0 := ne_of_gt hTpos
      field_simp [hT0]
      ring_nf
      nlinarith
    have hfin1 : (8 / T) * (300 * x * (Real.log x) ^ 2) + 8 * Real.log x * (100 * (x * Real.log x / T) + 100)
        ≤ 3200 * (x * (Real.log x) ^ 2 / T) + 800 * Real.log x := by
      calc
        (8 / T) * (300 * x * (Real.log x) ^ 2) + 8 * Real.log x * (100 * (x * Real.log x / T) + 100)
            ≤ 2400 * (x * (Real.log x) ^ 2 / T) + (800 * (x * (Real.log x) ^ 2 / T) + 800 * Real.log x) := by
              exact add_le_add h1 h2
        _ = 3200 * (x * (Real.log x) ^ 2 / T) + 800 * Real.log x := by ring
    have hfin2 : 3200 * (x * (Real.log x) ^ 2 / T) + 800 * Real.log x ≤
        8192 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
      have hpos1 : 0 ≤ x * (Real.log x) ^ 2 / T := div_nonneg (mul_nonneg hx0 (sq_nonneg _)) hTpos.le
      have hc1 : 3200 * (x * (Real.log x) ^ 2 / T) ≤ 8192 * (x * (Real.log x) ^ 2 / T) := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (3200 : ℝ) ≤ 8192) hpos1
      have hc2 : 800 * Real.log x ≤ 8192 * Real.log x := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (800 : ℝ) ≤ 8192) hL0
      have hc3 : 8192 * (x * (Real.log x) ^ 2 / T + Real.log x) =
          8192 * (x * (Real.log x) ^ 2 / T) + 8192 * Real.log x := by ring
      nlinarith [hc1, hc2, hc3]
    exact le_trans (le_trans htotal hfin1) hfin2


private def raw (x T : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
    min (1 : ℝ) (1 / (T * |Real.log (x / (n : ℝ))|))

private lemma tt_eq_raw {x T : ℝ} (n : ℕ) : tt x T n = raw x T n := by
  unfold tt raw lam rp kern
  ring

private lemma main_bound_equiv {x T : ℝ} (hx : 3 ≤ x) (hT : 2 ≤ T) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ∧
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
        8192 * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  have h := main_bound hx hT
  constructor
  · exact Summable.congr h.1 (fun n => (tt_eq_raw (x := x) (T := T) n).symm)
  · have hE : (∑' n : ℕ, raw x T n) = (∑' n : ℕ, tt x T n) := by
      apply tsum_congr
      intro n
      exact tt_eq_raw (x := x) (T := T) n
    change (∑' n : ℕ, raw x T n) ≤ 8192 * (x * (Real.log x) ^ 2 / T + Real.log x)
    rw [hE]
    exact h.2

theorem mangoldtPerronError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ∧
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x)) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
        C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  refine ⟨8192, by norm_num, ?_⟩
  intro x hx T hT
  exact main_bound_equiv hx hT

end Commons.NumberTheory.Zeta