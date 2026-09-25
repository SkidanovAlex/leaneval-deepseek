import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Lagarias.sigma_le_3224_range_1001_1079
import Submission.Commons.NumberTheory.Lagarias.sigma_le_3844_range_1080_1259
import Submission.Commons.NumberTheory.Lagarias.sigma_le_4368_range_1260_1439
import Submission.Commons.NumberTheory.Lagarias.sigma_le_4914_range_1440_1500

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def expLower (x : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℚ)

private def logOneAddLower (t : ℚ) : ℚ :=
  2 * t / (t + 2)

private def logTwoLower : ℚ := 6931471803 / 10000000000

private def logLowerAux (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 =>
      if x < 2 then logOneAddLower (x - 1)
      else logTwoLower + logLowerAux (x / 2) k

private def logLower (x : ℚ) : ℚ := logLowerAux x 20

private lemma expLower_nonneg {x : ℚ} (hx : 0 ≤ x) (N : ℕ) : 0 ≤ expLower x N := by
  unfold expLower
  refine Finset.sum_nonneg ?_
  intro i hi
  exact div_nonneg (pow_nonneg hx i) (by exact_mod_cast (le_of_lt (Nat.factorial_pos i)))

private lemma expLower_le_exp (x : ℚ) (hx : 0 ≤ x) (N : ℕ) :
    ((expLower x N : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLower
  have hxr : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have h := Real.sum_le_exp_of_nonneg (x := (x : ℝ)) hxr N
  rw [Rat.cast_sum]
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro i hi
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

private lemma logOneAddLower_le_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    ((logOneAddLower t : ℚ) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  unfold logOneAddLower
  have htr : 0 ≤ (t : ℝ) := by exact_mod_cast ht
  have h := Real.le_log_one_add_of_nonneg htr
  rw [Rat.cast_div, Rat.cast_mul]
  rw [Rat.cast_ofNat]
  rw [Rat.cast_add]
  exact h

private lemma logTwoLower_le_log_two : ((logTwoLower : ℚ) : ℝ) ≤ Real.log 2 := by
  unfold logTwoLower
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  exact le_of_lt h

private lemma logTwoLower_nonneg : 0 ≤ logTwoLower := by
  unfold logTwoLower
  norm_num

private lemma logLowerAux_nonneg : ∀ k : ℕ, ∀ x : ℚ, 1 ≤ x → 0 ≤ logLowerAux x k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [logLowerAux]
  | succ k ih =>
      intro x hx
      unfold logLowerAux
      by_cases h : x < 2
      · simp [h]
        have ht : 0 ≤ x - 1 := by linarith
        unfold logOneAddLower
        have hden : 0 < (x - 1) + 2 := by linarith
        exact div_nonneg (mul_nonneg zero_le_two ht) (le_of_lt hden)
      · simp [h]
        have hx2 : 2 ≤ x := by exact le_of_not_gt h
        have hxhalf : 1 ≤ x / 2 := by
          have hx2q : (2 : ℚ) ≤ x := by exact_mod_cast hx2
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          norm_num
          exact hx2q
        exact add_nonneg logTwoLower_nonneg (ih (x / 2) hxhalf)

private lemma logLower_nonneg (x : ℚ) (hx : 1 ≤ x) : 0 ≤ logLower x := by
  unfold logLower
  exact logLowerAux_nonneg 20 x hx

private lemma logLowerAux_le_log : ∀ k : ℕ, ∀ x : ℚ, 1 ≤ x →
    ((logLowerAux x k : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [logLowerAux]
      exact Real.log_nonneg (by exact_mod_cast hx)
  | succ k ih =>
      intro x hx
      unfold logLowerAux
      by_cases h : x < 2
      · simp [h]
        have ht : 0 ≤ x - 1 := by linarith
        have hle := logOneAddLower_le_log_one_add (x - 1) ht
        have harg : (1 : ℝ) + ((x - 1 : ℚ) : ℝ) = (x : ℝ) := by
          norm_cast
          ring
        simpa [harg] using hle
      · simp [h]
        have hx2 : 2 ≤ x := by exact le_of_not_gt h
        have hxhalf : 1 ≤ x / 2 := by
          have hx2q : (2 : ℚ) ≤ x := by exact_mod_cast hx2
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          norm_num
          exact hx2q
        have hx_eq : (x : ℝ) = 2 * ((x / 2 : ℚ) : ℝ) := by
          have hx_eq_q : x = (2 : ℚ) * (x / 2) := by
            field_simp [show (2 : ℚ) ≠ 0 by norm_num]
          norm_cast
        have hxhalf_ne : ((x / 2 : ℚ) : ℝ) ≠ 0 := by
          have hxhalf_pos : 0 < ((x / 2 : ℚ) : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one hxhalf)
          exact ne_of_gt hxhalf_pos
        have hlog_mul := Real.log_mul (x := (2 : ℝ)) (y := ((x / 2 : ℚ) : ℝ)) (by norm_num) hxhalf_ne
        have hlog_eq : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          rw [hx_eq]
          exact hlog_mul
        have hle_add := add_le_add logTwoLower_le_log_two (ih (x / 2) hxhalf)
        exact le_trans hle_add (le_of_eq hlog_eq.symm)

private lemma logLower_le_log (x : ℚ) (hx : 1 ≤ x) :
    ((logLower x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  unfold logLower
  exact logLowerAux_le_log 20 x hx

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

private lemma q_lower_le (q : ℚ) (C : ℕ) (hq1 : 1 ≤ q)
    (hC : ((C : ℕ) : ℚ) ≤ q + expLower q 18 * logLower q) :
    (C : ℝ) ≤ (q : ℝ) + Real.exp (q : ℝ) * Real.log (q : ℝ) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1
  have hE := expLower_le_exp q hq0 18
  have hL := logLower_le_log q hq1
  have hE_nonneg : 0 ≤ ((expLower q 18 : ℚ) : ℝ) := by exact_mod_cast expLower_nonneg hq0 18
  have hL_nonneg : 0 ≤ ((logLower q : ℚ) : ℝ) := by exact_mod_cast logLower_nonneg q hq1
  have hExp_pos : 0 ≤ Real.exp (q : ℝ) := by positivity
  have hmul := mul_le_mul hE hL hL_nonneg hExp_pos
  have hprod : ((expLower q 18 : ℚ) : ℝ) * ((logLower q : ℚ) : ℝ) ≤
      Real.exp (q : ℝ) * Real.log (q : ℝ) := by
    simpa [Rat.cast_mul] using hmul
  have hC' : (C : ℝ) ≤ (q : ℝ) + ((expLower q 18 : ℚ) : ℝ) * ((logLower q : ℚ) : ℝ) := by
    exact_mod_cast hC
  linarith

private lemma check_branch (n : ℕ) (q : ℚ) (C : ℕ) (hq1 : 1 ≤ q)
    (hq_harm : (q : ℝ) ≤ (harmonic n : ℝ))
    (hCq : ((C : ℕ) : ℚ) ≤ q + expLower q 18 * logLower q)
    (hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ C) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hsig : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hsig_nat
  have hC_le := q_lower_le q C hq1 hCq
  have hrhs := rhs_ge_q n q hq1 hq_harm
  linarith

theorem finite_check_range_1001_1500 (n : ℕ) (hn0 : 0 < n) (hL : 1001 ≤ n) (hU : n ≤ 1500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  by_cases h1 : n ≤ 1079
  · have hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 :=
      sigma_le_3224_range_1001_1079 n hL h1
    have hq1 : (1 : ℚ) ≤ 187 / 25 := by norm_num
    have hq_harm : ((187 / 25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
      have hmono := harmonic_mono_real hL
      have hqa : ((187 / 25 : ℚ) : ℝ) ≤ (harmonic 1001 : ℝ) := by
        norm_num [harmonic]
      exact hqa.trans hmono
    have hCq : ((3224 : ℕ) : ℚ) ≤ (187 / 25 : ℚ) + expLower (187 / 25) 18 * logLower (187 / 25) := by
      norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower, Finset.sum_range_succ]
    exact check_branch n (187 / 25) 3224 hq1 hq_harm hCq hsig_nat
  · by_cases h2 : n ≤ 1259
    · have hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 :=
        sigma_le_3844_range_1080_1259 n (by omega) h2
      have hq1 : (1 : ℚ) ≤ 189 / 25 := by norm_num
      have hq_harm : ((189 / 25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
        have hmono := harmonic_mono_real (show 1080 ≤ n by omega)
        have hqa : ((189 / 25 : ℚ) : ℝ) ≤ (harmonic 1080 : ℝ) := by
          norm_num [harmonic]
        exact hqa.trans hmono
      have hCq : ((3844 : ℕ) : ℚ) ≤ (189 / 25 : ℚ) + expLower (189 / 25) 18 * logLower (189 / 25) := by
        norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower, Finset.sum_range_succ]
      exact check_branch n (189 / 25) 3844 hq1 hq_harm hCq hsig_nat
    · by_cases h3 : n ≤ 1439
      · have hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 :=
          sigma_le_4368_range_1260_1439 n (by omega) h3
        have hq1 : (1 : ℚ) ≤ 771 / 100 := by norm_num
        have hq_harm : ((771 / 100 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
          have hmono := harmonic_mono_real (show 1260 ≤ n by omega)
          have hqa : ((771 / 100 : ℚ) : ℝ) ≤ (harmonic 1260 : ℝ) := by
            norm_num [harmonic]
          exact hqa.trans hmono
        have hCq : ((4368 : ℕ) : ℚ) ≤ (771 / 100 : ℚ) + expLower (771 / 100) 18 * logLower (771 / 100) := by
          norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower, Finset.sum_range_succ]
        exact check_branch n (771 / 100) 4368 hq1 hq_harm hCq hsig_nat
      · have hsig_nat : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4914 :=
          sigma_le_4914_range_1440_1500 n (show 1440 ≤ n by omega) hU
        have hq1 : (1 : ℚ) ≤ 196 / 25 := by norm_num
        have hq_harm : ((196 / 25 : ℚ) : ℝ) ≤ (harmonic n : ℝ) := by
          have hmono := harmonic_mono_real (show 1440 ≤ n by omega)
          have hqa : ((196 / 25 : ℚ) : ℝ) ≤ (harmonic 1440 : ℝ) := by
            norm_num [harmonic]
          exact hqa.trans hmono
        have hCq : ((4914 : ℕ) : ℚ) ≤ (196 / 25 : ℚ) + expLower (196 / 25) 18 * logLower (196 / 25) := by
          norm_num [expLower, logLower, logLowerAux, logOneAddLower, logTwoLower, Finset.sum_range_succ]
        exact check_branch n (196 / 25) 4914 hq1 hq_harm hCq hsig_nat

end Commons.NumberTheory.Lagarias