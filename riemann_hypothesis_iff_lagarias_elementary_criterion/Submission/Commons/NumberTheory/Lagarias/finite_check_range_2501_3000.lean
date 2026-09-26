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

private theorem sigma_le_9360_2501_2600_chk_2501 :
    (List.range' 2501 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2511 :
    (List.range' 2511 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2521 :
    (List.range' 2521 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2531 :
    (List.range' 2531 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2541 :
    (List.range' 2541 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2551 :
    (List.range' 2551 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2561 :
    (List.range' 2561 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2571 :
    (List.range' 2571 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2581 :
    (List.range' 2581 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private theorem sigma_le_9360_2501_2600_chk_2591 :
    (List.range' 2591 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9360) = true := by
  decide +kernel

private lemma sigma_le_9360_2501_2600 (n : ℕ) (ha : 2501 ≤ n) (hb : n ≤ 2600) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 9360 := by
  if h : n < 2511 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2501 n (by omega) h
  else
    if h : n < 2521 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2511 n (by omega) h
    else
      if h : n < 2531 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2521 n (by omega) h
      else
        if h : n < 2541 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2531 n (by omega) h
        else
          if h : n < 2551 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2541 n (by omega) h
          else
            if h : n < 2561 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2551 n (by omega) h
            else
              if h : n < 2571 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2561 n (by omega) h
              else
                if h : n < 2581 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2571 n (by omega) h
                else
                  if h : n < 2591 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2581 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9360_2501_2600_chk_2591 n (by omega) (by omega)

private theorem sigma_le_8928_2601_2700_chk_2601 :
    (List.range' 2601 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2611 :
    (List.range' 2611 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2621 :
    (List.range' 2621 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2631 :
    (List.range' 2631 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2641 :
    (List.range' 2641 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2651 :
    (List.range' 2651 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2661 :
    (List.range' 2661 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2671 :
    (List.range' 2671 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2681 :
    (List.range' 2681 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private theorem sigma_le_8928_2601_2700_chk_2691 :
    (List.range' 2691 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8928) = true := by
  decide +kernel

private lemma sigma_le_8928_2601_2700 (n : ℕ) (ha : 2601 ≤ n) (hb : n ≤ 2700) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 8928 := by
  if h : n < 2611 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2601 n (by omega) h
  else
    if h : n < 2621 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2611 n (by omega) h
    else
      if h : n < 2631 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2621 n (by omega) h
      else
        if h : n < 2641 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2631 n (by omega) h
        else
          if h : n < 2651 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2641 n (by omega) h
          else
            if h : n < 2661 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2651 n (by omega) h
            else
              if h : n < 2671 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2661 n (by omega) h
              else
                if h : n < 2681 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2671 n (by omega) h
                else
                  if h : n < 2691 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2681 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8928_2601_2700_chk_2691 n (by omega) (by omega)

private theorem sigma_le_8736_2701_2800_chk_2701 :
    (List.range' 2701 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2711 :
    (List.range' 2711 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2721 :
    (List.range' 2721 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2731 :
    (List.range' 2731 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2741 :
    (List.range' 2741 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2751 :
    (List.range' 2751 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2761 :
    (List.range' 2761 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2771 :
    (List.range' 2771 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2781 :
    (List.range' 2781 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private theorem sigma_le_8736_2701_2800_chk_2791 :
    (List.range' 2791 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 8736) = true := by
  decide +kernel

private lemma sigma_le_8736_2701_2800 (n : ℕ) (ha : 2701 ≤ n) (hb : n ≤ 2800) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 8736 := by
  if h : n < 2711 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2701 n (by omega) h
  else
    if h : n < 2721 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2711 n (by omega) h
    else
      if h : n < 2731 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2721 n (by omega) h
      else
        if h : n < 2741 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2731 n (by omega) h
        else
          if h : n < 2751 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2741 n (by omega) h
          else
            if h : n < 2761 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2751 n (by omega) h
            else
              if h : n < 2771 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2761 n (by omega) h
              else
                if h : n < 2781 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2771 n (by omega) h
                else
                  if h : n < 2791 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2781 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_8736_2701_2800_chk_2791 n (by omega) (by omega)

private theorem sigma_le_9906_2801_2900_chk_2801 :
    (List.range' 2801 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2811 :
    (List.range' 2811 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2821 :
    (List.range' 2821 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2831 :
    (List.range' 2831 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2841 :
    (List.range' 2841 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2851 :
    (List.range' 2851 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2861 :
    (List.range' 2861 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2871 :
    (List.range' 2871 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2881 :
    (List.range' 2881 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private theorem sigma_le_9906_2801_2900_chk_2891 :
    (List.range' 2891 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9906) = true := by
  decide +kernel

private lemma sigma_le_9906_2801_2900 (n : ℕ) (ha : 2801 ≤ n) (hb : n ≤ 2900) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 9906 := by
  if h : n < 2811 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2801 n (by omega) h
  else
    if h : n < 2821 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2811 n (by omega) h
    else
      if h : n < 2831 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2821 n (by omega) h
      else
        if h : n < 2841 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2831 n (by omega) h
        else
          if h : n < 2851 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2841 n (by omega) h
          else
            if h : n < 2861 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2851 n (by omega) h
            else
              if h : n < 2871 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2861 n (by omega) h
              else
                if h : n < 2881 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2871 n (by omega) h
                else
                  if h : n < 2891 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2881 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9906_2801_2900_chk_2891 n (by omega) (by omega)

private theorem sigma_le_9576_2901_3000_chk_2901 :
    (List.range' 2901 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2911 :
    (List.range' 2911 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2921 :
    (List.range' 2921 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2931 :
    (List.range' 2931 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2941 :
    (List.range' 2941 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2951 :
    (List.range' 2951 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2961 :
    (List.range' 2961 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2971 :
    (List.range' 2971 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2981 :
    (List.range' 2981 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private theorem sigma_le_9576_2901_3000_chk_2991 :
    (List.range' 2991 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 9576) = true := by
  decide +kernel

private lemma sigma_le_9576_2901_3000 (n : ℕ) (ha : 2901 ≤ n) (hb : n ≤ 3000) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 9576 := by
  if h : n < 2911 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2901 n (by omega) h
  else
    if h : n < 2921 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2911 n (by omega) h
    else
      if h : n < 2931 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2921 n (by omega) h
      else
        if h : n < 2941 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2931 n (by omega) h
        else
          if h : n < 2951 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2941 n (by omega) h
          else
            if h : n < 2961 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2951 n (by omega) h
            else
              if h : n < 2971 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2961 n (by omega) h
              else
                if h : n < 2981 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2971 n (by omega) h
                else
                  if h : n < 2991 then exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2981 n (by omega) h
                  else
                    exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_9576_2901_3000_chk_2991 n (by omega) (by omega)

private lemma hq_harm_2501 (n : ℕ) (hL : 2501 ≤ n) :
    ((42/5 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((42/5 : ℚ) : ℝ) ≤ (harmonic 2501 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2601 (n : ℕ) (hL : 2601 ≤ n) :
    ((211/25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((211/25 : ℚ) : ℝ) ≤ (harmonic 2601 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2701 (n : ℕ) (hL : 2701 ≤ n) :
    ((847/100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((847/100 : ℚ) : ℝ) ≤ (harmonic 2701 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2801 (n : ℕ) (hL : 2801 ≤ n) :
    ((851/100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((851/100 : ℚ) : ℝ) ≤ (harmonic 2801 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_2901 (n : ℕ) (hL : 2901 ≤ n) :
    ((171/20 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((171/20 : ℚ) : ℝ) ≤ (harmonic 2901 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hCq_2501 : ((9360 : ℕ) : ℚ) ≤ lowerRat (42/5) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2601 : ((8928 : ℕ) : ℚ) ≤ lowerRat (211/25) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2701 : ((8736 : ℕ) : ℚ) ≤ lowerRat (847/100) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2801 : ((9906 : ℕ) : ℚ) ≤ lowerRat (851/100) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_2901 : ((9576 : ℕ) : ℚ) ≤ lowerRat (171/20) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

theorem finite_check_range_2501_3000 (n : ℕ) (hn0 : 0 < n) (hL : 2501 ≤ n) (hU : n ≤ 3000) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases h1 : n ≤ 2600
  · exact check_branch n (42/5) 9360 (by norm_num) (hq_harm_2501 n hL) hCq_2501
      (sigma_le_9360_2501_2600 n hL h1)
  · by_cases h2 : n ≤ 2700
    · exact check_branch n (211/25) 8928 (by norm_num) (hq_harm_2601 n (by omega)) hCq_2601
        (sigma_le_8928_2601_2700 n (by omega) h2)
    · by_cases h3 : n ≤ 2800
      · exact check_branch n (847/100) 8736 (by norm_num) (hq_harm_2701 n (by omega)) hCq_2701
          (sigma_le_8736_2701_2800 n (by omega) h3)
      · by_cases h4 : n ≤ 2900
        · exact check_branch n (851/100) 9906 (by norm_num) (hq_harm_2801 n (by omega)) hCq_2801
            (sigma_le_9906_2801_2900 n (by omega) h4)
        · exact check_branch n (171/20) 9576 (by norm_num) (hq_harm_2901 n (by omega)) hCq_2901
            (sigma_le_9576_2901_3000 n (by omega) hU)

end Commons.NumberTheory.Lagarias
