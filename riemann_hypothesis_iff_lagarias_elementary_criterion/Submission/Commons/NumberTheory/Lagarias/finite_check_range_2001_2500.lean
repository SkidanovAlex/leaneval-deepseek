import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.SigmaCheck

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def expLowerRat (h : ℚ) (K : ℕ) : ℚ :=
  ∑ i ∈ Finset.range K, h ^ i / (Nat.factorial i : ℚ)

private def logLowerRat (h : ℚ) (M : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range M,
    (((h - 1) / (h + 1)) ^ (2 * i + 1)) / (2 * i + 1 : ℚ)

private def lowerRat (h : ℚ) : ℚ := h + expLowerRat h 14 * logLowerRat h 6

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
  have he : (expLowerRat h 14 : ℝ) ≤ Real.exp (h : ℝ) := exp_lower_bound_rat h hh 14
  have hl : (logLowerRat h 6 : ℝ) ≤ Real.log (h : ℝ) := log_lower_bound_rat h h1 6
  have he_nonneg : 0 ≤ (expLowerRat h 14 : ℝ) := expLowerRat_nonneg h hh 14
  have hl_nonneg : 0 ≤ (logLowerRat h 6 : ℝ) := logLowerRat_nonneg h h1 6
  have hmul : (expLowerRat h 14 : ℝ) * (logLowerRat h 6 : ℝ) ≤
      Real.exp (h : ℝ) * Real.log (h : ℝ) :=
    mul_le_mul he hl hl_nonneg (le_of_lt (Real.exp_pos _))
  have hlower : (lowerRat h : ℝ) =
      (h : ℝ) + (expLowerRat h 14 : ℝ) * (logLowerRat h 6 : ℝ) := by
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

private theorem sigma_le_6944_2001_2100_chk_2001 :
    (List.range' 2001 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2011 :
    (List.range' 2011 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2021 :
    (List.range' 2021 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2031 :
    (List.range' 2031 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2041 :
    (List.range' 2041 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2051 :
    (List.range' 2051 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2061 :
    (List.range' 2061 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2071 :
    (List.range' 2071 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2081 :
    (List.range' 2081 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private theorem sigma_le_6944_2001_2100_chk_2091 :
    (List.range' 2091 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 6944) = true := by
  decide +kernel

private lemma sigma_le_6944_2001_2100 (n : ℕ) (ha : 2001 ≤ n) (hb : n ≤ 2100) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 6944 := by
  if h : n < 2011 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2001 n (by omega) h
  else
    if h : n < 2021 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2011 n (by omega) h
    else
      if h : n < 2031 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2021 n (by omega) h
      else
        if h : n < 2041 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2031 n (by omega) h
        else
          if h : n < 2051 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2041 n (by omega) h
          else
            if h : n < 2061 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2051 n (by omega) h
            else
              if h : n < 2071 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2061 n (by omega) h
              else
                if h : n < 2081 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2071 n (by omega) h
                else
                  if h : n < 2091 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2081 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_6944_2001_2100_chk_2091 n (by omega) (by omega)

private theorem sigma_le_7440_2101_2200_chk_2101 :
    (List.range' 2101 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2111 :
    (List.range' 2111 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2121 :
    (List.range' 2121 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2131 :
    (List.range' 2131 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2141 :
    (List.range' 2141 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2151 :
    (List.range' 2151 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2161 :
    (List.range' 2161 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2171 :
    (List.range' 2171 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2181 :
    (List.range' 2181 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private theorem sigma_le_7440_2101_2200_chk_2191 :
    (List.range' 2191 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7440) = true := by
  decide +kernel

private lemma sigma_le_7440_2101_2200 (n : ℕ) (ha : 2101 ≤ n) (hb : n ≤ 2200) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 7440 := by
  if h : n < 2111 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2101 n (by omega) h
  else
    if h : n < 2121 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2111 n (by omega) h
    else
      if h : n < 2131 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2121 n (by omega) h
      else
        if h : n < 2141 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2131 n (by omega) h
        else
          if h : n < 2151 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2141 n (by omega) h
          else
            if h : n < 2161 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2151 n (by omega) h
            else
              if h : n < 2171 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2161 n (by omega) h
              else
                if h : n < 2181 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2171 n (by omega) h
                else
                  if h : n < 2191 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2181 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7440_2101_2200_chk_2191 n (by omega) (by omega)

private theorem sigma_le_7200_2201_2300_chk_2201 :
    (List.range' 2201 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2211 :
    (List.range' 2211 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2221 :
    (List.range' 2221 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2231 :
    (List.range' 2231 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2241 :
    (List.range' 2241 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2251 :
    (List.range' 2251 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2261 :
    (List.range' 2261 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2271 :
    (List.range' 2271 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2281 :
    (List.range' 2281 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private theorem sigma_le_7200_2201_2300_chk_2291 :
    (List.range' 2291 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7200) = true := by
  decide +kernel

private lemma sigma_le_7200_2201_2300 (n : ℕ) (ha : 2201 ≤ n) (hb : n ≤ 2300) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 7200 := by
  if h : n < 2211 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2201 n (by omega) h
  else
    if h : n < 2221 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2211 n (by omega) h
    else
      if h : n < 2231 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2221 n (by omega) h
      else
        if h : n < 2241 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2231 n (by omega) h
        else
          if h : n < 2251 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2241 n (by omega) h
          else
            if h : n < 2261 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2251 n (by omega) h
            else
              if h : n < 2271 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2261 n (by omega) h
              else
                if h : n < 2281 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2271 n (by omega) h
                else
                  if h : n < 2291 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2281 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7200_2201_2300_chk_2291 n (by omega) (by omega)

private theorem sigma_le_7812_2301_2400_chk_2301 :
    (List.range' 2301 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2311 :
    (List.range' 2311 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2321 :
    (List.range' 2321 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2331 :
    (List.range' 2331 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2341 :
    (List.range' 2341 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2351 :
    (List.range' 2351 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2361 :
    (List.range' 2361 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2371 :
    (List.range' 2371 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2381 :
    (List.range' 2381 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private theorem sigma_le_7812_2301_2400_chk_2391 :
    (List.range' 2391 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7812) = true := by
  decide +kernel

private lemma sigma_le_7812_2301_2400 (n : ℕ) (ha : 2301 ≤ n) (hb : n ≤ 2400) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 7812 := by
  if h : n < 2311 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2301 n (by omega) h
  else
    if h : n < 2321 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2311 n (by omega) h
    else
      if h : n < 2331 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2321 n (by omega) h
      else
        if h : n < 2341 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2331 n (by omega) h
        else
          if h : n < 2351 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2341 n (by omega) h
          else
            if h : n < 2361 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2351 n (by omega) h
            else
              if h : n < 2371 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2361 n (by omega) h
              else
                if h : n < 2381 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2371 n (by omega) h
                else
                  if h : n < 2391 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2381 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7812_2301_2400_chk_2391 n (by omega) (by omega)

private theorem sigma_le_7254_2401_2500_chk_2401 :
    (List.range' 2401 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2411 :
    (List.range' 2411 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2421 :
    (List.range' 2421 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2431 :
    (List.range' 2431 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2441 :
    (List.range' 2441 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2451 :
    (List.range' 2451 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2461 :
    (List.range' 2461 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2471 :
    (List.range' 2471 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2481 :
    (List.range' 2481 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private theorem sigma_le_7254_2401_2500_chk_2491 :
    (List.range' 2491 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 7254) = true := by
  decide +kernel

private lemma sigma_le_7254_2401_2500 (n : ℕ) (ha : 2401 ≤ n) (hb : n ≤ 2500) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 7254 := by
  if h : n < 2411 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2401 n (by omega) h
  else
    if h : n < 2421 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2411 n (by omega) h
    else
      if h : n < 2431 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2421 n (by omega) h
      else
        if h : n < 2441 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2431 n (by omega) h
        else
          if h : n < 2451 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2441 n (by omega) h
          else
            if h : n < 2461 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2451 n (by omega) h
            else
              if h : n < 2471 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2461 n (by omega) h
              else
                if h : n < 2481 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2471 n (by omega) h
                else
                  if h : n < 2491 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2481 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_7254_2401_2500_chk_2491 n (by omega) (by omega)
private lemma hq_harm_2001 (n : ℕ) (hL : 2001 ≤ n) :
    ((163/20 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((163/20 : ℚ) : ℝ) ≤ (harmonic 2001 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2101 (n : ℕ) (hL : 2101 ≤ n) :
    ((411/50 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((411/50 : ℚ) : ℝ) ≤ (harmonic 2101 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2201 (n : ℕ) (hL : 2201 ≤ n) :
    ((41/5 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((41/5 : ℚ) : ℝ) ≤ (harmonic 2201 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2301 (n : ℕ) (hL : 2301 ≤ n) :
    ((83/10 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((83/10 : ℚ) : ℝ) ≤ (harmonic 2301 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2401 (n : ℕ) (hL : 2401 ≤ n) :
    ((83/10 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((83/10 : ℚ) : ℝ) ≤ (harmonic 2401 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hCq_2001 : ((6944 : ℕ) : ℚ) ≤ lowerRat (163/20) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2101 : ((7440 : ℕ) : ℚ) ≤ lowerRat (411/50) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2201 : ((7200 : ℕ) : ℚ) ≤ lowerRat (41/5) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2301 : ((7812 : ℕ) : ℚ) ≤ lowerRat (83/10) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2401 : ((7254 : ℕ) : ℚ) ≤ lowerRat (83/10) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

theorem finite_check_range_2001_2500 (n : ℕ) (hn0 : 0 < n) (hL : 2001 ≤ n) (hU : n ≤ 2500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases h1 : n ≤ 2100
  · exact check_branch n (163/20) 6944 (by norm_num) (hq_harm_2001 n hL) hCq_2001
      (sigma_le_6944_2001_2100 n hL h1)
  · by_cases h2 : n ≤ 2200
    · exact check_branch n (411/50) 7440 (by norm_num) (hq_harm_2101 n (by omega)) hCq_2101
        (sigma_le_7440_2101_2200 n (by omega) h2)
    · by_cases h3 : n ≤ 2300
      · exact check_branch n (41/5) 7200 (by norm_num) (hq_harm_2201 n (by omega)) hCq_2201
          (sigma_le_7200_2201_2300 n (by omega) h3)
      · by_cases h4 : n ≤ 2400
        · exact check_branch n (83/10) 7812 (by norm_num) (hq_harm_2301 n (by omega)) hCq_2301
            (sigma_le_7812_2301_2400 n (by omega) h4)
        · exact check_branch n (83/10) 7254 (by norm_num) (hq_harm_2401 n (by omega)) hCq_2401
            (sigma_le_7254_2401_2500 n (by omega) hU)

end Commons.NumberTheory.Lagarias