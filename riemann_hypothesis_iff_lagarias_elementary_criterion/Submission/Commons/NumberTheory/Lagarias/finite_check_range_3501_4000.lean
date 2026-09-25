import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Lagarias.sigma_le_12493_range_3501_3600
import Submission.Commons.NumberTheory.Lagarias.sigma_le_11904_range_3601_3700
import Submission.Commons.NumberTheory.Lagarias.sigma_le_13440_range_3701_3800
import Submission.Commons.NumberTheory.Lagarias.sigma_le_12264_range_3801_3900
import Submission.Commons.NumberTheory.Lagarias.sigma_le_14040_range_3901_4000

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def expLowerRat (h : ℚ) (K : ℕ) : ℚ :=
  ∑ i ∈ Finset.range K, h ^ i / (Nat.factorial i : ℚ)

private def logLowerRat (h : ℚ) (M : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range M,
    (((h - 1) / (h + 1)) ^ (2 * i + 1)) / (2 * i + 1 : ℚ)

private def lowerRat (h : ℚ) : ℚ := h + expLowerRat h 15 * logLowerRat h 5

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
  have he : (expLowerRat h 15 : ℝ) ≤ Real.exp (h : ℝ) := exp_lower_bound_rat h hh 15
  have hl : (logLowerRat h 5 : ℝ) ≤ Real.log (h : ℝ) := log_lower_bound_rat h h1 5
  have he_nonneg : 0 ≤ (expLowerRat h 15 : ℝ) := expLowerRat_nonneg h hh 15
  have hl_nonneg : 0 ≤ (logLowerRat h 5 : ℝ) := logLowerRat_nonneg h h1 5
  have hmul : (expLowerRat h 15 : ℝ) * (logLowerRat h 5 : ℝ) ≤
      Real.exp (h : ℝ) * Real.log (h : ℝ) :=
    mul_le_mul he hl hl_nonneg (le_of_lt (Real.exp_pos _))
  have hlower : (lowerRat h : ℝ) =
      (h : ℝ) + (expLowerRat h 15 : ℝ) * (logLowerRat h 5 : ℝ) := by
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

private lemma hq_harm_3501 (n : ℕ) (hL : 3501 ≤ n) :
    ((873/100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((873/100 : ℚ) : ℝ) ≤ (harmonic 3501 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_3601 (n : ℕ) (hL : 3601 ≤ n) :
    ((219/25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((219/25 : ℚ) : ℝ) ≤ (harmonic 3601 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_3701 (n : ℕ) (hL : 3701 ≤ n) :
    ((879/100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((879/100 : ℚ) : ℝ) ≤ (harmonic 3701 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_3801 (n : ℕ) (hL : 3801 ≤ n) :
    ((441/50 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((441/50 : ℚ) : ℝ) ≤ (harmonic 3801 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hq_harm_3901 (n : ℕ) (hL : 3901 ≤ n) :
    ((221/25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
  have hmono := harmonic_mono_real hL
  have hqa : ((221/25 : ℚ) : ℝ) ≤ (harmonic 3901 : ℝ) := by
    norm_num [harmonic]
  exact hqa.trans hmono

private lemma hCq_3501 : ((12493 : ℕ) : ℚ) ≤ lowerRat (873/100) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_3601 : ((11904 : ℕ) : ℚ) ≤ lowerRat (219/25) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_3701 : ((13440 : ℕ) : ℚ) ≤ lowerRat (879/100) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_3801 : ((12264 : ℕ) : ℚ) ≤ lowerRat (441/50) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

private lemma hCq_3901 : ((14040 : ℕ) : ℚ) ≤ lowerRat (221/25) := by
  norm_num [lowerRat, expLowerRat, logLowerRat, Finset.sum_range_succ]

theorem finite_check_range_3501_4000 (n : ℕ) (hn0 : 0 < n) (hL : 3501 ≤ n) (hU : n ≤ 4000) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases h1 : n ≤ 3600
  · exact check_branch n (873/100) 12493 (by norm_num) (hq_harm_3501 n hL) hCq_3501
      (sigma_le_12493_range_3501_3600 n hL h1)
  · by_cases h2 : n ≤ 3700
    · exact check_branch n (219/25) 11904 (by norm_num) (hq_harm_3601 n (by omega)) hCq_3601
        (sigma_le_11904_range_3601_3700 n (by omega) h2)
    · by_cases h3 : n ≤ 3800
      · exact check_branch n (879/100) 13440 (by norm_num) (hq_harm_3701 n (by omega)) hCq_3701
          (sigma_le_13440_range_3701_3800 n (by omega) h3)
      · by_cases h4 : n ≤ 3900
        · exact check_branch n (441/50) 12264 (by norm_num) (hq_harm_3801 n (by omega)) hCq_3801
            (sigma_le_12264_range_3801_3900 n (by omega) h4)
        · exact check_branch n (221/25) 14040 (by norm_num) (hq_harm_3901 n (by omega)) hCq_3901
            (sigma_le_14040_range_3901_4000 n (by omega) hU)

end Commons.NumberTheory.Lagarias
