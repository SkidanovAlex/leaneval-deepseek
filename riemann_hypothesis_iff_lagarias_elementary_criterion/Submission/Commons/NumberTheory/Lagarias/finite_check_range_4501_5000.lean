import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.SigmaCheck

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def expLowerRat (h : ℚ) (K : ℕ) : ℚ :=
  ∑ i ∈ Finset.range K, h ^ i / (Nat.factorial i : ℚ)

private def logLowerRat (h : ℚ) (M : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range M,
    (((h - 1) / (h + 1)) ^ (2 * i + 1)) / (2 * i + 1 : ℚ)

private def lowerRat (h : ℚ) : ℚ := h + expLowerRat h 18 * logLowerRat h 6

private def sigmaFastAux : ℕ → ℕ → ℕ
  | _n, 0 => 0
  | n, k + 1 => sigmaFastAux n k + if n % (k + 1) = 0 then (k + 1) else 0

private def sigmaFast (n : ℕ) : ℕ := sigmaFastAux n n

private lemma sigmaFastAux_eq_sum (n k : ℕ) :
    sigmaFastAux n k = ∑ i ∈ Finset.Ico 1 (k + 1), if i ∣ n then i else 0 := by
  induction k with
  | zero =>
      simp [sigmaFastAux]
  | succ k ih =>
      rw [sigmaFastAux]
      rw [ih]
      rw [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega)]
      simp [Nat.dvd_iff_mod_eq_zero, add_comm]

private lemma sigma_eq_sigmaFast (n : ℕ) : (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

private lemma exp_lower_bound_rat (h : ℚ) (hh : 0 ≤ h) (K : ℕ) :
    (expLowerRat h K : ℝ) ≤ Real.exp (h : ℝ) := by
  have hcast : (expLowerRat h K : ℝ) =
      ∑ i ∈ Finset.range K, (h : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    simp [expLowerRat]
  rw [hcast]
  simpa using (Real.sum_le_exp_of_nonneg (by exact_mod_cast hh) K)

private lemma log_lower_bound_rat (h : ℚ) (h1 : 1 < h) (M : ℕ) :
    (logLowerRat h M : ℝ) ≤ Real.log (h : ℝ) := by
  let x : ℝ := (((h - 1 : ℚ) / (h + 1 : ℚ) : ℚ) : ℝ)
  have hx0 : 0 ≤ x := by
    have hnum : (0 : ℚ) ≤ h - 1 := by linarith
    have hden : (0 : ℚ) < h + 1 := by linarith
    have hfrac : (0 : ℚ) ≤ (h - 1) / (h + 1) := div_nonneg hnum (le_of_lt hden)
    simpa [x] using
      (show (0 : ℝ) ≤ (((h - 1 : ℚ) / (h + 1 : ℚ) : ℚ) : ℝ) by exact_mod_cast hfrac)
  have hx1 : x < 1 := by
    have hnum : (h - 1 : ℚ) < h + 1 := by linarith
    have hden : (0 : ℚ) < h + 1 := by linarith
    have hfrac : ((h - 1 : ℚ) / (h + 1) : ℚ) < 1 := by
      rw [div_lt_one hden]
      exact hnum
    simpa [x] using
      (show (((h - 1 : ℚ) / (h + 1 : ℚ) : ℚ) : ℝ) < 1 by exact_mod_cast hfrac)
  have hS := Real.sum_range_le_log_div hx0 hx1 M
  have hlog : 2 * (∑ i ∈ Finset.range M, x ^ (2 * i + 1) / (2 * i + 1)) ≤
      Real.log (h : ℝ) := by
    have hdiv_rat : ((1 + (h - 1) / (h + 1)) / (1 - (h - 1) / (h + 1)) : ℚ) = h := by
      field_simp [show (h + 1 : ℚ) ≠ 0 by linarith]
      ring
    have hdiv : (1 + x) / (1 - x) = (h : ℝ) := by
      have hdiv_real :
          (((1 + (h - 1) / (h + 1)) / (1 - (h - 1) / (h + 1)) : ℚ) : ℝ) = (h : ℝ) := by
        exact_mod_cast hdiv_rat
      simpa [x] using hdiv_real
    have hmul : 2 * (∑ i ∈ Finset.range M, x ^ (2 * i + 1) / (2 * i + 1)) ≤
        Real.log ((1 + x) / (1 - x)) := by
      nlinarith [hS]
    simpa [hdiv] using hmul
  have hcast : (logLowerRat h M : ℝ) =
      2 * (∑ i ∈ Finset.range M, x ^ (2 * i + 1) / (2 * i + 1)) := by
    simp [logLowerRat, x]
  rw [hcast]
  exact hlog

private lemma expLowerRat_nonneg (h : ℚ) (hh : 0 ≤ h) (K : ℕ) : 0 ≤ (expLowerRat h K : ℝ) := by
  have hcast : (expLowerRat h K : ℝ) =
      ∑ i ∈ Finset.range K, (h : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    simp [expLowerRat]
  rw [hcast]
  exact Finset.sum_nonneg (s := Finset.range K) (by
    intro i _
    exact div_nonneg (pow_nonneg (by exact_mod_cast hh) i) (by positivity))

private lemma logLowerRat_nonneg (h : ℚ) (h1 : 1 < h) (M : ℕ) : 0 ≤ (logLowerRat h M : ℝ) := by
  have hnum : (0 : ℚ) ≤ h - 1 := by linarith
  have hden : (0 : ℚ) < h + 1 := by linarith
  have hfrac : (0 : ℚ) ≤ (h - 1) / (h + 1) := div_nonneg hnum (le_of_lt hden)
  have hx0 : 0 ≤ (((h - 1 : ℚ) / (h + 1 : ℚ) : ℚ) : ℝ) := by exact_mod_cast hfrac
  have hsum : 0 ≤ (∑ i ∈ Finset.range M,
      (((h - 1) / (h + 1) : ℚ) : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℝ)) := by
    exact Finset.sum_nonneg (s := Finset.range M) (by
      intro i _
      exact div_nonneg (pow_nonneg hx0 (2 * i + 1)) (by positivity))
  have hcast : (logLowerRat h M : ℝ) =
      2 * (∑ i ∈ Finset.range M,
        (((h - 1) / (h + 1) : ℚ) : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℝ)) := by
    simp [logLowerRat]
  rw [hcast]
  exact mul_nonneg (by norm_num) hsum

private lemma rhs_lower_bound_rat (h : ℚ) (h1 : 1 < h) :
    (lowerRat h : ℝ) ≤ (h : ℝ) + Real.exp (h : ℝ) * Real.log (h : ℝ) := by
  have hh : 0 ≤ h := by linarith
  have he : (expLowerRat h 18 : ℝ) ≤ Real.exp (h : ℝ) := exp_lower_bound_rat h hh 18
  have hl : (logLowerRat h 6 : ℝ) ≤ Real.log (h : ℝ) := log_lower_bound_rat h h1 6
  have he_nonneg : 0 ≤ (expLowerRat h 18 : ℝ) := expLowerRat_nonneg h hh 18
  have hl_nonneg : 0 ≤ (logLowerRat h 6 : ℝ) := logLowerRat_nonneg h h1 6
  have hmul : (expLowerRat h 18 : ℝ) * (logLowerRat h 6 : ℝ) ≤
      Real.exp (h : ℝ) * Real.log (h : ℝ) :=
    mul_le_mul he hl hl_nonneg (le_of_lt (Real.exp_pos _))
  have hlower : (lowerRat h : ℝ) =
      (h : ℝ) + (expLowerRat h 18 : ℝ) * (logLowerRat h 6 : ℝ) := by
    simp [lowerRat]
  rw [hlower]
  linarith

private lemma harmonic_mono_real {a n : ℕ} (ha : a ≤ n) :
    (harmonic a : ℝ) ≤ (harmonic n : ℝ) := by
  have hQ : (harmonic a : ℚ) ≤ harmonic n := by
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.Icc_subset_Icc (le_refl 1) ha
    · intro i hi hnot
      positivity
  exact_mod_cast hQ

private lemma rhs_ge_q (n : ℕ) (q : ℚ) (hqpos : 1 ≤ q) (hqn : (q : ℝ) ≤ (harmonic n : ℝ)) :
    (q : ℝ) + Real.exp (q : ℝ) * Real.log (q : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hqpos)
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hqpos)
  have hexp_le : Real.exp (q : ℝ) ≤ Real.exp (harmonic n : ℝ) :=
    Real.exp_le_exp.mpr hqn
  have hlog_le : Real.log (q : ℝ) ≤ Real.log (harmonic n : ℝ) :=
    Real.log_le_log hq0 hqn
  have hmul := mul_le_mul hexp_le hlog_le hlogq_nonneg (Real.exp_pos (harmonic n : ℝ)).le
  exact add_le_add hqn hmul

private lemma q_lower_le (q : ℚ) (C : ℕ) (hq1 : 1 < q)
    (hC : ((C : ℕ) : ℚ) ≤ lowerRat q) :
    (C : ℝ) ≤ (q : ℝ) + Real.exp (q : ℝ) * Real.log (q : ℝ) := by
  have hlower := rhs_lower_bound_rat q hq1
  have hC' : (C : ℝ) ≤ (lowerRat q : ℝ) := by
    exact_mod_cast hC
  linarith

private lemma check_branch (n : ℕ) (q : ℚ) (C : ℕ) (hq1 : 1 < q)
    (hq_harm : (q : ℝ) ≤ (harmonic n : ℝ))
    (hCq : ((C : ℕ) : ℚ) ≤ lowerRat q)
    (hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ C) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hsig : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hsig_nat
  have hC_le := q_lower_le q C hq1 hCq
  have hrhs := rhs_ge_q n q (le_of_lt hq1) hq_harm
  linarith

private theorem sigma_le_16380_4501_4520_chk_4501 :
    (List.range' 4501 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4501_4520_chk_4511 :
    (List.range' 4511 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4501_4520 (n : ℕ) (ha : 4501 ≤ n) (hb : n ≤ 4520) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4511 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4501_4520_chk_4501 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4501_4520_chk_4511 n (by omega) (by omega)

private theorem sigma_le_16380_4521_4540_chk_4521 :
    (List.range' 4521 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4521_4540_chk_4531 :
    (List.range' 4531 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4521_4540 (n : ℕ) (ha : 4521 ≤ n) (hb : n ≤ 4540) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4531 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4521_4540_chk_4521 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4521_4540_chk_4531 n (by omega) (by omega)

private theorem sigma_le_16380_4541_4560_chk_4541 :
    (List.range' 4541 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4541_4560_chk_4551 :
    (List.range' 4551 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4541_4560 (n : ℕ) (ha : 4541 ≤ n) (hb : n ≤ 4560) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4551 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4541_4560_chk_4541 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4541_4560_chk_4551 n (by omega) (by omega)

private theorem sigma_le_16380_4561_4580_chk_4561 :
    (List.range' 4561 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4561_4580_chk_4571 :
    (List.range' 4571 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4561_4580 (n : ℕ) (ha : 4561 ≤ n) (hb : n ≤ 4580) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4571 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4561_4580_chk_4561 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4561_4580_chk_4571 n (by omega) (by omega)

private theorem sigma_le_16380_4581_4600_chk_4581 :
    (List.range' 4581 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4581_4600_chk_4591 :
    (List.range' 4591 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4581_4600 (n : ℕ) (ha : 4581 ≤ n) (hb : n ≤ 4600) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4591 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4581_4600_chk_4581 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4581_4600_chk_4591 n (by omega) (by omega)

private theorem sigma_le_16380_4601_4620_chk_4601 :
    (List.range' 4601 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4601_4620_chk_4611 :
    (List.range' 4611 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4601_4620 (n : ℕ) (ha : 4601 ≤ n) (hb : n ≤ 4620) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4611 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4601_4620_chk_4601 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4601_4620_chk_4611 n (by omega) (by omega)

private theorem sigma_le_16380_4621_4640_chk_4621 :
    (List.range' 4621 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4621_4640_chk_4631 :
    (List.range' 4631 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4621_4640 (n : ℕ) (ha : 4621 ≤ n) (hb : n ≤ 4640) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4631 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4621_4640_chk_4621 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4621_4640_chk_4631 n (by omega) (by omega)

private theorem sigma_le_16380_4641_4660_chk_4641 :
    (List.range' 4641 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4641_4660_chk_4651 :
    (List.range' 4651 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4641_4660 (n : ℕ) (ha : 4641 ≤ n) (hb : n ≤ 4660) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4651 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4641_4660_chk_4641 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4641_4660_chk_4651 n (by omega) (by omega)

private theorem sigma_le_16380_4661_4680_chk_4661 :
    (List.range' 4661 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4661_4680_chk_4671 :
    (List.range' 4671 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4661_4680 (n : ℕ) (ha : 4661 ≤ n) (hb : n ≤ 4680) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4671 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4661_4680_chk_4661 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4661_4680_chk_4671 n (by omega) (by omega)

private theorem sigma_le_16380_4681_4700_chk_4681 :
    (List.range' 4681 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4681_4700_chk_4691 :
    (List.range' 4691 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4681_4700 (n : ℕ) (ha : 4681 ≤ n) (hb : n ≤ 4700) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4691 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4681_4700_chk_4681 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4681_4700_chk_4691 n (by omega) (by omega)

private theorem sigma_le_16380_4701_4720_chk_4701 :
    (List.range' 4701 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4701_4720_chk_4711 :
    (List.range' 4711 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4701_4720 (n : ℕ) (ha : 4701 ≤ n) (hb : n ≤ 4720) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4711 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4701_4720_chk_4701 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4701_4720_chk_4711 n (by omega) (by omega)

private theorem sigma_le_16380_4721_4740_chk_4721 :
    (List.range' 4721 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4721_4740_chk_4731 :
    (List.range' 4731 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4721_4740 (n : ℕ) (ha : 4721 ≤ n) (hb : n ≤ 4740) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4731 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4721_4740_chk_4721 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4721_4740_chk_4731 n (by omega) (by omega)

private theorem sigma_le_16380_4741_4760_chk_4741 :
    (List.range' 4741 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4741_4760_chk_4751 :
    (List.range' 4751 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4741_4760 (n : ℕ) (ha : 4741 ≤ n) (hb : n ≤ 4760) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4751 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4741_4760_chk_4741 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4741_4760_chk_4751 n (by omega) (by omega)

private theorem sigma_le_16380_4761_4780_chk_4761 :
    (List.range' 4761 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4761_4780_chk_4771 :
    (List.range' 4771 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4761_4780 (n : ℕ) (ha : 4761 ≤ n) (hb : n ≤ 4780) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4771 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4761_4780_chk_4761 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4761_4780_chk_4771 n (by omega) (by omega)

private theorem sigma_le_16380_4781_4800_chk_4781 :
    (List.range' 4781 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4781_4800_chk_4791 :
    (List.range' 4791 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4781_4800 (n : ℕ) (ha : 4781 ≤ n) (hb : n ≤ 4800) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4791 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4781_4800_chk_4781 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4781_4800_chk_4791 n (by omega) (by omega)

private theorem sigma_le_16380_4801_4820_chk_4801 :
    (List.range' 4801 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4801_4820_chk_4811 :
    (List.range' 4811 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4801_4820 (n : ℕ) (ha : 4801 ≤ n) (hb : n ≤ 4820) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4811 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4801_4820_chk_4801 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4801_4820_chk_4811 n (by omega) (by omega)

private theorem sigma_le_16380_4821_4840_chk_4821 :
    (List.range' 4821 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4821_4840_chk_4831 :
    (List.range' 4831 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4821_4840 (n : ℕ) (ha : 4821 ≤ n) (hb : n ≤ 4840) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4831 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4821_4840_chk_4821 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4821_4840_chk_4831 n (by omega) (by omega)

private theorem sigma_le_16380_4841_4860_chk_4841 :
    (List.range' 4841 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4841_4860_chk_4851 :
    (List.range' 4851 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4841_4860 (n : ℕ) (ha : 4841 ≤ n) (hb : n ≤ 4860) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4851 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4841_4860_chk_4841 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4841_4860_chk_4851 n (by omega) (by omega)

private theorem sigma_le_16380_4861_4880_chk_4861 :
    (List.range' 4861 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4861_4880_chk_4871 :
    (List.range' 4871 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4861_4880 (n : ℕ) (ha : 4861 ≤ n) (hb : n ≤ 4880) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4871 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4861_4880_chk_4861 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4861_4880_chk_4871 n (by omega) (by omega)

private theorem sigma_le_16380_4881_4900_chk_4881 :
    (List.range' 4881 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4881_4900_chk_4891 :
    (List.range' 4891 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4881_4900 (n : ℕ) (ha : 4881 ≤ n) (hb : n ≤ 4900) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4891 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4881_4900_chk_4881 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4881_4900_chk_4891 n (by omega) (by omega)

private theorem sigma_le_16380_4901_4920_chk_4901 :
    (List.range' 4901 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4901_4920_chk_4911 :
    (List.range' 4911 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4901_4920 (n : ℕ) (ha : 4901 ≤ n) (hb : n ≤ 4920) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4911 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4901_4920_chk_4901 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4901_4920_chk_4911 n (by omega) (by omega)

private theorem sigma_le_16380_4921_4940_chk_4921 :
    (List.range' 4921 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4921_4940_chk_4931 :
    (List.range' 4931 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4921_4940 (n : ℕ) (ha : 4921 ≤ n) (hb : n ≤ 4940) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4931 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4921_4940_chk_4921 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4921_4940_chk_4931 n (by omega) (by omega)

private theorem sigma_le_16380_4941_4960_chk_4941 :
    (List.range' 4941 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4941_4960_chk_4951 :
    (List.range' 4951 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4941_4960 (n : ℕ) (ha : 4941 ≤ n) (hb : n ≤ 4960) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4951 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4941_4960_chk_4941 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4941_4960_chk_4951 n (by omega) (by omega)

private theorem sigma_le_16380_4961_4980_chk_4961 :
    (List.range' 4961 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4961_4980_chk_4971 :
    (List.range' 4971 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4961_4980 (n : ℕ) (ha : 4961 ≤ n) (hb : n ≤ 4980) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4971 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4961_4980_chk_4961 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4961_4980_chk_4971 n (by omega) (by omega)

private theorem sigma_le_16380_4981_5000_chk_4981 :
    (List.range' 4981 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private theorem sigma_le_16380_4981_5000_chk_4991 :
    (List.range' 4991 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 16380) = true := by
  decide +kernel

private lemma sigma_le_16380_4981_5000 (n : ℕ) (ha : 4981 ≤ n) (hb : n ≤ 5000) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  if h : n < 4991 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4981_5000_chk_4981 n (by omega) h
  else
    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_16380_4981_5000_chk_4991 n (by omega) (by omega)

private lemma sigma_le_16380_range_4501_5000 (n : ℕ) (hL : 4501 ≤ n) (hU : n ≤ 5000) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 16380 := by
  by_cases h1 : n ≤ 4520
  · exact sigma_le_16380_4501_4520 n hL h1
  · by_cases h2 : n ≤ 4540
    · exact sigma_le_16380_4521_4540 n (by omega) h2
    · by_cases h3 : n ≤ 4560
      · exact sigma_le_16380_4541_4560 n (by omega) h3
      · by_cases h4 : n ≤ 4580
        · exact sigma_le_16380_4561_4580 n (by omega) h4
        · by_cases h5 : n ≤ 4600
          · exact sigma_le_16380_4581_4600 n (by omega) h5
          · by_cases h6 : n ≤ 4620
            · exact sigma_le_16380_4601_4620 n (by omega) h6
            · by_cases h7 : n ≤ 4640
              · exact sigma_le_16380_4621_4640 n (by omega) h7
              · by_cases h8 : n ≤ 4660
                · exact sigma_le_16380_4641_4660 n (by omega) h8
                · by_cases h9 : n ≤ 4680
                  · exact sigma_le_16380_4661_4680 n (by omega) h9
                  · by_cases h10 : n ≤ 4700
                    · exact sigma_le_16380_4681_4700 n (by omega) h10
                    · by_cases h11 : n ≤ 4720
                      · exact sigma_le_16380_4701_4720 n (by omega) h11
                      · by_cases h12 : n ≤ 4740
                        · exact sigma_le_16380_4721_4740 n (by omega) h12
                        · by_cases h13 : n ≤ 4760
                          · exact sigma_le_16380_4741_4760 n (by omega) h13
                          · by_cases h14 : n ≤ 4780
                            · exact sigma_le_16380_4761_4780 n (by omega) h14
                            · by_cases h15 : n ≤ 4800
                              · exact sigma_le_16380_4781_4800 n (by omega) h15
                              · by_cases h16 : n ≤ 4820
                                · exact sigma_le_16380_4801_4820 n (by omega) h16
                                · by_cases h17 : n ≤ 4840
                                  · exact sigma_le_16380_4821_4840 n (by omega) h17
                                  · by_cases h18 : n ≤ 4860
                                    · exact sigma_le_16380_4841_4860 n (by omega) h18
                                    · by_cases h19 : n ≤ 4880
                                      · exact sigma_le_16380_4861_4880 n (by omega) h19
                                      · by_cases h20 : n ≤ 4900
                                        · exact sigma_le_16380_4881_4900 n (by omega) h20
                                        · by_cases h21 : n ≤ 4920
                                          · exact sigma_le_16380_4901_4920 n (by omega) h21
                                          · by_cases h22 : n ≤ 4940
                                            · exact sigma_le_16380_4921_4940 n (by omega) h22
                                            · by_cases h23 : n ≤ 4960
                                              · exact sigma_le_16380_4941_4960 n (by omega) h23
                                              · by_cases h24 : n ≤ 4980
                                                · exact sigma_le_16380_4961_4980 n (by omega) h24
                                                · exact sigma_le_16380_4981_5000 n (by omega) hU
private lemma hq_harm_4501 (n : ℕ) (hL : 4501 ≤ n) :
    ((449/50 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((449/50 : ℚ) : ℝ) ≤ (harmonic 4501 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hCq_4501 : ((16380 : ℕ) : ℚ) ≤ lowerRat (449/50) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

theorem finite_check_range_4501_5000 (n : ℕ) (hn0 : 0 < n) (hL : 4501 ≤ n) (hU : n ≤ 5000) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  exact check_branch n (449/50) 16380 (by norm_num) (hq_harm_4501 n hL) hCq_4501
      (sigma_le_16380_range_4501_5000 n hL hU)

end Commons.NumberTheory.Lagarias
