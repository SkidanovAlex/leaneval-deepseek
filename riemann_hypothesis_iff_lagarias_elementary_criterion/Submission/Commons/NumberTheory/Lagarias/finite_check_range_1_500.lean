import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Lagarias

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

private def rhsLower (n : ℕ) : ℚ :=
  let H := harmonic n
  H + expLower H 18 * logLower H

private def finiteCert (n : ℕ) : Bool :=
  decide (((ArithmeticFunction.sigma 1 n : ℕ) : ℚ) ≤ rhsLower n)

private lemma one_le_harmonic {n : ℕ} (hn : 0 < n) : 1 ≤ harmonic n := by
  rw [harmonic_eq_sum_Icc]
  have hmem : 1 ∈ Finset.Icc 1 n := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsingle := Finset.single_le_sum (s := Finset.Icc 1 n) (f := fun i : ℕ => (i : ℚ)⁻¹) ?_ hmem
  · simpa using hsingle
  · intro i hi
    positivity

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
          have hx_eq_q : x = (2:ℚ) * (x / 2) := by
            field_simp [show (2:ℚ) ≠ 0 by norm_num]
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

private lemma rhsLower_le (n : ℕ) (hn : 0 < n) :
    ((rhsLower n : ℚ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  set H : ℚ := harmonic n
  have hH1 : 1 ≤ H := by
    simpa [H] using one_le_harmonic hn
  have hH0 : 0 ≤ H := le_trans zero_le_one hH1
  have hexp_low := expLower_le_exp H hH0 18
  have hexp_nonneg_q := expLower_nonneg (x := H) hH0 18
  have hexp_nonneg : 0 ≤ ((expLower H 18 : ℚ) : ℝ) := by exact_mod_cast hexp_nonneg_q
  have hlog_low := logLower_le_log H hH1
  have hlog_nonneg_q := logLower_nonneg H hH1
  have hlog_nonneg : 0 ≤ ((logLower H : ℚ) : ℝ) := by exact_mod_cast hlog_nonneg_q
  have hexp_pos : 0 ≤ Real.exp (H : ℝ) := by positivity
  have hmul := mul_le_mul hexp_low hlog_low hlog_nonneg hexp_pos
  have hadd := add_le_add_left hmul (H : ℝ)
  simpa [H, rhsLower, Rat.cast_add, Rat.cast_mul] using hadd

private lemma finiteCert_implies (n : ℕ) (hc : finiteCert n = true) (hn : 0 < n) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hq : ((ArithmeticFunction.sigma 1 n : ℕ) : ℚ) ≤ rhsLower n := by
    unfold finiteCert at hc
    exact of_decide_eq_true hc
  have hq_cast : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (rhsLower n : ℝ) := by
    exact_mod_cast hq
  exact le_trans hq_cast (rhsLower_le n hn)


set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_mem_Icc_1_100 : ∀ k ∈ Finset.Icc 1 100, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_mem_Icc_101_200 : ∀ k ∈ Finset.Icc 101 200, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_mem_Icc_201_300 : ∀ k ∈ Finset.Icc 201 300, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_mem_Icc_301_400 : ∀ k ∈ Finset.Icc 301 400, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_mem_Icc_401_500 : ∀ k ∈ Finset.Icc 401 500, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

private lemma finiteCert_mem_Icc_1_500 : ∀ k ∈ Finset.Icc 1 500, finiteCert k = true := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk2 : k ≤ 500 := (Finset.mem_Icc.mp hk).2
  by_cases h1 : k ≤ 100
  · exact finiteCert_mem_Icc_1_100 k (Finset.mem_Icc.mpr ⟨hk1, h1⟩)
  · have h101 : 101 ≤ k := by omega
    by_cases h2 : k ≤ 200
    · exact finiteCert_mem_Icc_101_200 k (Finset.mem_Icc.mpr ⟨h101, h2⟩)
    · have h201 : 201 ≤ k := by omega
      by_cases h3 : k ≤ 300
      · exact finiteCert_mem_Icc_201_300 k (Finset.mem_Icc.mpr ⟨h201, h3⟩)
      · have h301 : 301 ≤ k := by omega
        by_cases h4 : k ≤ 400
        · exact finiteCert_mem_Icc_301_400 k (Finset.mem_Icc.mpr ⟨h301, h4⟩)
        · have h401 : 401 ≤ k := by omega
          exact finiteCert_mem_Icc_401_500 k (Finset.mem_Icc.mpr ⟨h401, hk2⟩)

private theorem finite_check_aux_le_500 (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hmem : n ∈ Finset.Icc 1 500 := by
    exact Finset.mem_Icc.mpr ⟨by omega, hn⟩
  exact finiteCert_implies n (finiteCert_mem_Icc_1_500 n hmem) hn0

theorem finite_check_range_1_500 (n : ℕ) (hn0 : 0 < n) (hL : 1 ≤ n) (hU : n ≤ 500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have _ : 1 ≤ n := hL
  exact finite_check_aux_le_500 n hn0 hU

end Commons.NumberTheory.Lagarias