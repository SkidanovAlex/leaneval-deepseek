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


/-! The certificate is checked in chunks of ten values, one declaration each, which keeps the
kernel's term size per declaration small. -/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_1 : ∀ k ∈ Finset.Icc 1 10, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_11 : ∀ k ∈ Finset.Icc 11 20, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_21 : ∀ k ∈ Finset.Icc 21 30, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_31 : ∀ k ∈ Finset.Icc 31 40, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_41 : ∀ k ∈ Finset.Icc 41 50, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_51 : ∀ k ∈ Finset.Icc 51 60, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_61 : ∀ k ∈ Finset.Icc 61 70, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_71 : ∀ k ∈ Finset.Icc 71 80, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_81 : ∀ k ∈ Finset.Icc 81 90, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_91 : ∀ k ∈ Finset.Icc 91 100, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_101 : ∀ k ∈ Finset.Icc 101 110, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_111 : ∀ k ∈ Finset.Icc 111 120, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_121 : ∀ k ∈ Finset.Icc 121 130, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_131 : ∀ k ∈ Finset.Icc 131 140, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_141 : ∀ k ∈ Finset.Icc 141 150, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_151 : ∀ k ∈ Finset.Icc 151 160, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_161 : ∀ k ∈ Finset.Icc 161 170, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_171 : ∀ k ∈ Finset.Icc 171 180, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_181 : ∀ k ∈ Finset.Icc 181 190, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_191 : ∀ k ∈ Finset.Icc 191 200, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_201 : ∀ k ∈ Finset.Icc 201 210, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_211 : ∀ k ∈ Finset.Icc 211 220, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_221 : ∀ k ∈ Finset.Icc 221 230, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_231 : ∀ k ∈ Finset.Icc 231 240, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_241 : ∀ k ∈ Finset.Icc 241 250, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_251 : ∀ k ∈ Finset.Icc 251 260, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_261 : ∀ k ∈ Finset.Icc 261 270, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_271 : ∀ k ∈ Finset.Icc 271 280, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_281 : ∀ k ∈ Finset.Icc 281 290, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_291 : ∀ k ∈ Finset.Icc 291 300, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_301 : ∀ k ∈ Finset.Icc 301 310, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_311 : ∀ k ∈ Finset.Icc 311 320, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_321 : ∀ k ∈ Finset.Icc 321 330, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_331 : ∀ k ∈ Finset.Icc 331 340, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_341 : ∀ k ∈ Finset.Icc 341 350, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_351 : ∀ k ∈ Finset.Icc 351 360, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_361 : ∀ k ∈ Finset.Icc 361 370, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_371 : ∀ k ∈ Finset.Icc 371 380, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_381 : ∀ k ∈ Finset.Icc 381 390, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_391 : ∀ k ∈ Finset.Icc 391 400, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_401 : ∀ k ∈ Finset.Icc 401 410, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_411 : ∀ k ∈ Finset.Icc 411 420, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_421 : ∀ k ∈ Finset.Icc 421 430, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_431 : ∀ k ∈ Finset.Icc 431 440, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_441 : ∀ k ∈ Finset.Icc 441 450, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_451 : ∀ k ∈ Finset.Icc 451 460, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_461 : ∀ k ∈ Finset.Icc 461 470, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_471 : ∀ k ∈ Finset.Icc 471 480, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_481 : ∀ k ∈ Finset.Icc 481 490, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private lemma finiteCert_chk_491 : ∀ k ∈ Finset.Icc 491 500, finiteCert k = true := by
  unfold finiteCert rhsLower expLower logLower logLowerAux logOneAddLower logTwoLower harmonic ArithmeticFunction.sigma Nat.divisors
  decide +kernel

private lemma finiteCert_mem_Icc_1_500 : ∀ k ∈ Finset.Icc 1 500, finiteCert k = true := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk2 : k ≤ 500 := (Finset.mem_Icc.mp hk).2
  if h1 : k ≤ 250 then
    if h2 : k ≤ 120 then
      if h3 : k ≤ 60 then
        if h4 : k ≤ 30 then
          if h5 : k ≤ 10 then
            exact finiteCert_chk_1 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 20 then
              exact finiteCert_chk_11 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_21 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 40 then
            exact finiteCert_chk_31 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 50 then
              exact finiteCert_chk_41 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_51 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      else
        if h4 : k ≤ 90 then
          if h5 : k ≤ 70 then
            exact finiteCert_chk_61 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 80 then
              exact finiteCert_chk_71 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_81 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 100 then
            exact finiteCert_chk_91 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 110 then
              exact finiteCert_chk_101 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_111 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    else
      if h3 : k ≤ 180 then
        if h4 : k ≤ 150 then
          if h5 : k ≤ 130 then
            exact finiteCert_chk_121 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 140 then
              exact finiteCert_chk_131 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_141 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 160 then
            exact finiteCert_chk_151 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 170 then
              exact finiteCert_chk_161 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_171 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      else
        if h4 : k ≤ 210 then
          if h5 : k ≤ 190 then
            exact finiteCert_chk_181 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 200 then
              exact finiteCert_chk_191 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_201 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 230 then
            if h6 : k ≤ 220 then
              exact finiteCert_chk_211 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_221 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 240 then
              exact finiteCert_chk_231 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_241 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  else
    if h2 : k ≤ 370 then
      if h3 : k ≤ 310 then
        if h4 : k ≤ 280 then
          if h5 : k ≤ 260 then
            exact finiteCert_chk_251 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 270 then
              exact finiteCert_chk_261 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_271 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 290 then
            exact finiteCert_chk_281 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 300 then
              exact finiteCert_chk_291 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_301 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      else
        if h4 : k ≤ 340 then
          if h5 : k ≤ 320 then
            exact finiteCert_chk_311 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 330 then
              exact finiteCert_chk_321 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_331 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 350 then
            exact finiteCert_chk_341 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 360 then
              exact finiteCert_chk_351 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_361 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    else
      if h3 : k ≤ 430 then
        if h4 : k ≤ 400 then
          if h5 : k ≤ 380 then
            exact finiteCert_chk_371 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 390 then
              exact finiteCert_chk_381 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_391 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 410 then
            exact finiteCert_chk_401 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 420 then
              exact finiteCert_chk_411 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_421 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      else
        if h4 : k ≤ 460 then
          if h5 : k ≤ 440 then
            exact finiteCert_chk_431 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 450 then
              exact finiteCert_chk_441 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_451 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        else
          if h5 : k ≤ 480 then
            if h6 : k ≤ 470 then
              exact finiteCert_chk_461 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_471 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          else
            if h6 : k ≤ 490 then
              exact finiteCert_chk_481 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            else
              exact finiteCert_chk_491 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

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