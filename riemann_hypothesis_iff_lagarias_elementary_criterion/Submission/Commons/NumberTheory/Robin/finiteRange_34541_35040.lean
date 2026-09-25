import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Star

open scoped BigOperators

set_option maxRecDepth 10000

/-! Certified rational lower/upper bounds for `log`, `exp` and Euler's constant γ,
    used to verify Robin's inequality on the finite range `34541 ≤ n ≤ 35040` by
    computation.  All the machinery below is `private`: it is module-local. -/

namespace Commons.NumberTheory.Robin

private def logOneAddV (t : ℚ) : ℚ := t / (2 + t)
private noncomputable def logOneAddVR (t : ℝ) : ℝ := t / (2 + t)

private noncomputable def logOneAddLowerR (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range 14, (logOneAddVR t) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

private noncomputable def logOneAddUpperR (t : ℝ) : ℝ :=
  2 * ((∑ i ∈ Finset.range 14, (logOneAddVR t) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
    (logOneAddVR t) ^ (2 * 14 + 1) / (1 - (logOneAddVR t) ^ 2))

private def logOneAddLower (t : ℚ) : ℚ :=
  2 * (∑ i ∈ Finset.range 14, (logOneAddV t) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ))

private def logOneAddUpper (t : ℚ) : ℚ :=
  2 * ((∑ i ∈ Finset.range 14, (logOneAddV t) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)) +
    (logOneAddV t) ^ (2 * 14 + 1) / (1 - (logOneAddV t) ^ 2))

private def logTwoLowerQ : ℚ := 6931471803 / 10000000000
private def logTwoUpperQ : ℚ := 6931471808 / 10000000000

private def logDepth : ℕ := 40

private def logLowerAux : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then logOneAddLower (x - 1) else 0
  | x, k + 1 =>
      if x < 2 then logOneAddLower (x - 1)
      else logTwoLowerQ + logLowerAux (x / 2) k

private def logLower (x : ℚ) : ℚ := logLowerAux x logDepth

private def logUpperAux : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then logOneAddUpper (x - 1) else 0
  | x, k + 1 =>
      if x < 2 then logOneAddUpper (x - 1)
      else logTwoUpperQ + logUpperAux (x / 2) k

private def logUpper (x : ℚ) : ℚ := logUpperAux x logDepth

private def expLower (x : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℚ)

private def gammaLowerQ : ℚ := 23 / 40

private def expGammaLowerQ : ℚ := expLower gammaLowerQ 24

private def logLogLower (n : ℚ) : ℚ := logLower (max (logLower n) 1)

private def robinRhsLower (n : ℕ) : ℚ :=
  expGammaLowerQ * (n : ℚ) * logLogLower (n : ℚ)

private lemma logOneAddV_nonneg {t : ℚ} (ht : 0 ≤ t) : 0 ≤ logOneAddV t := by
  unfold logOneAddV
  positivity

private lemma logOneAddV_lt_one {t : ℚ} (ht : 0 ≤ t) : logOneAddV t < 1 := by
  unfold logOneAddV
  have hden : 0 < 2 + t := by linarith
  rw [div_lt_one hden]
  linarith

private lemma logOneAddVR_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logOneAddVR t := by
  unfold logOneAddVR
  positivity

private lemma logOneAddVR_lt_one {t : ℝ} (ht : 0 ≤ t) : logOneAddVR t < 1 := by
  unfold logOneAddVR
  have hden : 0 < 2 + t := by linarith
  rw [div_lt_one hden]
  linarith

private lemma logOneAddVR_eq {t : ℝ} (ht : 0 ≤ t) :
    (1 + logOneAddVR t) / (1 - logOneAddVR t) = 1 + t := by
  unfold logOneAddVR
  have hd : 2 + t ≠ 0 := by linarith
  field_simp [hd]
  ring

private lemma logOneAddLowerR_le_log_one_add (t : ℝ) (ht : 0 ≤ t) :
    logOneAddLowerR t ≤ Real.log (1 + t) := by
  have hv0 : 0 ≤ logOneAddVR t := logOneAddVR_nonneg ht
  have hv1 : logOneAddVR t < 1 := logOneAddVR_lt_one ht
  have hmain := Real.sum_range_le_log_div (x := logOneAddVR t) hv0 hv1 14
  have hvr : (1 + logOneAddVR t) / (1 - logOneAddVR t) = 1 + t := logOneAddVR_eq ht
  calc
    logOneAddLowerR t ≤ 2 * (1 / 2 * Real.log ((1 + logOneAddVR t) / (1 - logOneAddVR t))) := by
      unfold logOneAddLowerR
      exact (mul_le_mul_of_nonneg_left hmain (by norm_num))
    _ = Real.log (1 + t) := by
      rw [hvr]
      ring

private lemma logOneAddUpperR_ge_log_one_add (t : ℝ) (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ logOneAddUpperR t := by
  have hv0 : 0 ≤ logOneAddVR t := logOneAddVR_nonneg ht
  have hv1 : logOneAddVR t < 1 := logOneAddVR_lt_one ht
  have hmain := Real.log_div_le_sum_range_add (x := logOneAddVR t) hv0 hv1 14
  have hvr : (1 + logOneAddVR t) / (1 - logOneAddVR t) = 1 + t := logOneAddVR_eq ht
  calc
    Real.log (1 + t) = 2 * (1 / 2 * Real.log ((1 + logOneAddVR t) / (1 - logOneAddVR t))) := by
      rw [← hvr]
      ring
    _ ≤ logOneAddUpperR t := by
      unfold logOneAddUpperR
      exact (mul_le_mul_of_nonneg_left hmain (by norm_num))

private lemma cast_v {t : ℚ} : ((logOneAddV t : ℚ) : ℝ) = logOneAddVR (t : ℝ) := by
  simp [logOneAddV, logOneAddVR]

private lemma logOneAddLower_cast (t : ℚ) :
    ((logOneAddLower t : ℚ) : ℝ) = logOneAddLowerR (t : ℝ) := by
  rw [logOneAddLower, logOneAddLowerR]
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  rw [Rat.cast_sum]
  simp only [Rat.cast_div, Rat.cast_pow, cast_v]
  norm_num

private lemma logOneAddUpper_cast (t : ℚ) :
    ((logOneAddUpper t : ℚ) : ℝ) = logOneAddUpperR (t : ℝ) := by
  rw [logOneAddUpper, logOneAddUpperR]
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_sub]
  rw [Rat.cast_sum]
  simp only [Rat.cast_div, Rat.cast_pow, cast_v]
  norm_num
  rw [cast_v]

private lemma logOneAddLower_le_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    ((logOneAddLower t : ℚ) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  rw [logOneAddLower_cast]
  exact logOneAddLowerR_le_log_one_add (t : ℝ) (by exact_mod_cast ht)

private lemma logOneAddUpper_ge_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    Real.log (1 + (t : ℝ)) ≤ ((logOneAddUpper t : ℚ) : ℝ) := by
  rw [logOneAddUpper_cast]
  exact logOneAddUpperR_ge_log_one_add (t : ℝ) (by exact_mod_cast ht)

private lemma logTwoLowerQ_le_log_two : ((logTwoLowerQ : ℚ) : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num [logTwoLowerQ] at h ⊢
  exact le_of_lt h

private lemma logTwoUpperQ_ge_log_two : Real.log 2 ≤ ((logTwoUpperQ : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num [logTwoUpperQ] at h ⊢
  exact le_of_lt h

private lemma logTwoLowerQ_nonneg : 0 ≤ logTwoLowerQ := by norm_num [logTwoLowerQ]
private lemma logTwoUpperQ_nonneg : 0 ≤ logTwoUpperQ := by norm_num [logTwoUpperQ]

private lemma logOneAddLower_nonneg (t : ℚ) (ht : 0 ≤ t) : 0 ≤ logOneAddLower t := by
  unfold logOneAddLower
  have hv : 0 ≤ logOneAddV t := logOneAddV_nonneg ht
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (pow_nonneg hv (2 * i + 1))
    (le_of_lt (by exact_mod_cast (show 0 < 2 * i + 1 by omega)))

private lemma logOneAddUpper_nonneg (t : ℚ) (ht : 0 ≤ t) : 0 ≤ logOneAddUpper t := by
  unfold logOneAddUpper
  have hv : 0 ≤ logOneAddV t := logOneAddV_nonneg ht
  have hvlt : logOneAddV t < 1 := logOneAddV_lt_one ht
  have hv2 : 0 < 1 - (logOneAddV t) ^ 2 := by
    nlinarith [sq_nonneg (logOneAddV t)]
  have hsum : 0 ≤ (∑ i ∈ Finset.range 14,
      (logOneAddV t) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)) := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (pow_nonneg hv (2 * i + 1))
      (le_of_lt (by exact_mod_cast (show 0 < 2 * i + 1 by omega)))
  have htail : 0 ≤ (logOneAddV t) ^ (2 * 14 + 1) / (1 - (logOneAddV t) ^ 2) := by
    exact div_nonneg (pow_nonneg hv (2 * 14 + 1)) (le_of_lt hv2)
  exact mul_nonneg (by norm_num) (add_nonneg hsum htail)

private lemma logLowerAux_nonneg (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logLowerAux x k := by
  induction k generalizing x with
  | zero =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        simp [logLowerAux, hx2]
        exact logOneAddLower_nonneg (x - 1) ht0
      · simp [logLowerAux, hx2]
  | succ k ih =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        simp [logLowerAux, hx2]
        exact logOneAddLower_nonneg (x - 1) ht0
      · have hx2' : 2 ≤ x := le_of_not_gt hx2
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa using hx2'
        simp [logLowerAux, hx2]
        exact add_nonneg logTwoLowerQ_nonneg (ih (x / 2) hhalf1)

private lemma logUpperAux_nonneg (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logUpperAux x k := by
  induction k generalizing x with
  | zero =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        simp [logUpperAux, hx2]
        exact logOneAddUpper_nonneg (x - 1) ht0
      · simp [logUpperAux, hx2]
  | succ k ih =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        simp [logUpperAux, hx2]
        exact logOneAddUpper_nonneg (x - 1) ht0
      · have hx2' : 2 ≤ x := le_of_not_gt hx2
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa using hx2'
        simp [logUpperAux, hx2]
        exact add_nonneg logTwoUpperQ_nonneg (ih (x / 2) hhalf1)

private lemma logLowerAux_le_log (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ k) :
    ((logLowerAux x k : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using hx
      linarith
  | succ k ih =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        have hxcast : (x : ℝ) = 1 + ((x - 1 : ℚ) : ℝ) := by norm_num
        simp [logLowerAux, hx2]
        rw [hxcast]
        exact logOneAddLower_le_log_one_add (x - 1) ht0
      · have hx2' : 2 ≤ x := le_of_not_gt hx2
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa using hx2'
        have hhalf : x / 2 < 2 ^ k := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hx
        have hih := ih (x / 2) hhalf1 hhalf
        have hlog : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          have hhalfpos : ((x / 2 : ℚ) : ℝ) ≠ 0 := by
            have : 0 < ((x / 2 : ℚ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hhalf1)
            exact ne_of_gt this
          have hmul := Real.log_mul (x := (2 : ℝ)) (y := ((x / 2 : ℚ) : ℝ)) (by norm_num) hhalfpos
          have hxeq : (x : ℝ) = (2 : ℝ) * ((x / 2 : ℚ) : ℝ) := by
            have hq : x = (2 : ℚ) * (x / 2) := by ring
            exact_mod_cast hq
          rw [hxeq]
          exact hmul
        have hsum : ((logTwoLowerQ + logLowerAux (x / 2) k : ℚ) : ℝ) ≤
            Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          simpa using (add_le_add logTwoLowerQ_le_log_two hih)
        rw [hlog]
        simpa [logLowerAux, hx2] using hsum

private lemma logLower_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logLower x := by
  unfold logLower
  exact logLowerAux_nonneg logDepth x hx1

private lemma logUpper_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logUpper x := by
  unfold logUpper
  exact logUpperAux_nonneg logDepth x hx1

private lemma logLower_le_log (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    ((logLower x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  unfold logLower
  exact logLowerAux_le_log logDepth x hx1 hx

private lemma logUpperAux_ge_log (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ k) :
    Real.log (x : ℝ) ≤ ((logUpperAux x k : ℚ) : ℝ) := by
  induction k generalizing x with
  | zero =>
      have : (x : ℚ) < 1 := by simpa using hx
      linarith
  | succ k ih =>
      by_cases hx2 : x < 2
      · have ht0 : 0 ≤ x - 1 := by linarith
        have hxcast : (x : ℝ) = 1 + ((x - 1 : ℚ) : ℝ) := by norm_num
        simp [logUpperAux, hx2]
        rw [hxcast]
        exact logOneAddUpper_ge_log_one_add (x - 1) ht0
      · have hx2' : 2 ≤ x := le_of_not_gt hx2
        have hhalf1 : 1 ≤ x / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa using hx2'
        have hhalf : x / 2 < 2 ^ k := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 2)]
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hx
        have hih := ih (x / 2) hhalf1 hhalf
        have hlog : Real.log (x : ℝ) = Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) := by
          have hhalfpos : ((x / 2 : ℚ) : ℝ) ≠ 0 := by
            have : 0 < ((x / 2 : ℚ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hhalf1)
            exact ne_of_gt this
          have hmul := Real.log_mul (x := (2 : ℝ)) (y := ((x / 2 : ℚ) : ℝ)) (by norm_num) hhalfpos
          have hxeq : (x : ℝ) = (2 : ℝ) * ((x / 2 : ℚ) : ℝ) := by
            have hq : x = (2 : ℚ) * (x / 2) := by ring
            exact_mod_cast hq
          rw [hxeq]
          exact hmul
        have hsum : Real.log 2 + Real.log ((x / 2 : ℚ) : ℝ) ≤
            ((logTwoUpperQ + logUpperAux (x / 2) k : ℚ) : ℝ) := by
          simpa using (add_le_add logTwoUpperQ_ge_log_two hih)
        rw [hlog]
        simpa [logUpperAux, hx2] using hsum

private lemma logUpper_ge_log (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    Real.log (x : ℝ) ≤ ((logUpper x : ℚ) : ℝ) := by
  unfold logUpper
  exact logUpperAux_ge_log logDepth x hx1 hx

private lemma expLower_le_exp (x : ℚ) (hx : 0 ≤ x) (N : ℕ) :
    ((expLower x N : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLower
  have hxr : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have h := Real.sum_le_exp_of_nonneg (x := (x : ℝ)) hxr N
  rw [Rat.cast_sum]
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro i hi
  rw [Rat.cast_div, Rat.cast_pow]
  congr 1
  norm_num

private def gammaCert (m : ℕ) : ℚ := (harmonic m : ℚ) - logUpper (m + 1 : ℕ)

private lemma gammaCert_le_seq (m : ℕ) (hm : (1 : ℚ) ≤ (m + 1 : ℕ)) (hm2 : ((m + 1 : ℕ) : ℚ) < 2 ^ logDepth) :
    ((gammaCert m : ℚ) : ℝ) ≤ Real.eulerMascheroniSeq m := by
  unfold gammaCert
  rw [Rat.cast_sub]
  rw [Real.eulerMascheroniSeq]
  have hlogup : Real.log ((m : ℝ) + 1) ≤ ((logUpper (m + 1 : ℕ) : ℚ) : ℝ) := by
    simpa [Nat.cast_add] using
      (logUpper_ge_log ((m + 1 : ℕ) : ℚ) hm hm2)
  linarith

set_option maxHeartbeats 0 in
private lemma gammaCert_ge_23_40 : (23 / 40 : ℚ) ≤ gammaCert 300 := by
  unfold gammaCert logUpper logUpperAux logOneAddUpper logOneAddV logTwoUpperQ logDepth
  decide +kernel

private lemma gamma_gt_23_40 : (23 / 40 : ℝ) < Real.eulerMascheroniConstant := by
  have hseq : Real.eulerMascheroniSeq 300 < Real.eulerMascheroniConstant :=
    Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 300
  have hcert : ((gammaCert 300 : ℚ) : ℝ) ≤ Real.eulerMascheroniSeq 300 :=
    gammaCert_le_seq 300 (by norm_num) (by norm_num [logDepth])
  have h23 : (23 / 40 : ℝ) ≤ ((gammaCert 300 : ℚ) : ℝ) := by
    have hq : (23 : ℚ) ≤ 40 * gammaCert 300 := by
      have := gammaCert_ge_23_40
      nlinarith
    have hr : (23 : ℝ) ≤ (40 : ℝ) * ((gammaCert 300 : ℚ) : ℝ) := by
      exact_mod_cast hq
    nlinarith
  exact lt_of_le_of_lt (le_trans h23 hcert) hseq

private lemma gammaLowerQ_le_gamma : (gammaLowerQ : ℝ) ≤ Real.eulerMascheroniConstant := by
  unfold gammaLowerQ
  simpa using (le_of_lt gamma_gt_23_40)

private lemma expGammaLowerQ_le_exp_gamma : (expGammaLowerQ : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  unfold expGammaLowerQ
  have h1 : ((expLower (23 / 40 : ℚ) 24 : ℚ) : ℝ) ≤ Real.exp ((23 / 40 : ℚ) : ℝ) :=
    expLower_le_exp (23 / 40 : ℚ) (by norm_num) 24
  have h2 : Real.exp ((23 / 40 : ℚ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    exact Real.exp_le_exp.mpr gammaLowerQ_le_gamma
  exact le_trans h1 h2

private lemma expGammaLowerQ_nonneg : 0 ≤ expGammaLowerQ := by
  unfold expGammaLowerQ expLower
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (pow_nonneg (by norm_num : 0 ≤ (23 / 40 : ℚ)) i)
    (le_of_lt (by exact_mod_cast (Nat.factorial_pos i)))

private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [← Real.log_exp (1 : ℝ)]
  exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three

private lemma log_ge_one_of_ge_three (x : ℚ) (hx : 3 ≤ x) : (1 : ℝ) ≤ Real.log (x : ℝ) := by
  have hmono : Real.log (3 : ℝ) ≤ Real.log (x : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  exact le_trans (le_of_lt log_three_gt_one) hmono

private lemma logLogLower_nonneg (x : ℚ) (hx : 1 ≤ x) : 0 ≤ logLogLower x := by
  unfold logLogLower
  exact logLower_nonneg (max (logLower x) 1) (le_max_right _ _)

private lemma logLogLower_le_log_log (x : ℚ) (hx3 : 3 ≤ x) (hx2 : x < 2 ^ logDepth) :
    ((logLogLower x : ℚ) : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
  unfold logLogLower
  let a : ℚ := max (logLower x) 1
  have ha1 : 1 ≤ a := le_max_right _ _
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hx1)
  have hlogx : ((logLower x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := logLower_le_log x hx1 hx2
  have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := log_ge_one_of_ge_three x hx3
  have ha_le_logx : ((a : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
    unfold a
    by_cases h : logLower x ≤ 1
    · simp [h]
      exact hlogx1
    · have hlt : 1 < logLower x := lt_of_not_ge h
      have hcast : (1 : ℝ) ≤ ((logLower x : ℚ) : ℝ) := by exact_mod_cast (le_of_lt hlt)
      simp [le_of_lt hlt]
      exact hlogx
  have ha2 : a < 2 ^ logDepth := by
    have hlogxlt : Real.log (x : ℝ) < (x : ℝ) := by
      have hle : Real.log (x : ℝ) ≤ (x : ℝ) - 1 := Real.log_le_sub_one_of_pos hxpos
      linarith
    have hcastlt : ((logLower x : ℚ) : ℝ) < ((2 ^ logDepth : ℚ) : ℝ) := by
      have hxlt : (x : ℝ) < ((2 ^ logDepth : ℚ) : ℝ) := by exact_mod_cast hx2
      have hlogle : Real.log (x : ℝ) ≤ (x : ℝ) - 1 := Real.log_le_sub_one_of_pos hxpos
      nlinarith
    have hl : (logLower x : ℚ) < 2 ^ logDepth := by exact_mod_cast hcastlt
    have h1 : (1 : ℚ) < 2 ^ logDepth := by norm_num [logDepth]
    unfold a
    exact max_lt hl h1
  have hll1 : ((logLower a : ℚ) : ℝ) ≤ Real.log ((a : ℚ) : ℝ) := logLower_le_log a ha1 ha2
  have hlogpos : 0 < ((a : ℚ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ha1)
  have hmono : Real.log ((a : ℚ) : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
    exact Real.log_le_log hlogpos (by exact_mod_cast ha_le_logx)
  have hcomb : ((logLower a : ℚ) : ℝ) ≤ Real.log (Real.log (x : ℝ)) := le_trans hll1 hmono
  simpa [a] using hcomb

private lemma robinRhsLower_le (n : ℕ) (hn : 7901 ≤ n) (hn2 : n ≤ 55440) :
    (robinRhsLower n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  have hnn : 0 ≤ (n : ℚ) := by exact_mod_cast (show 0 ≤ n by omega)
  have hll0 : 0 ≤ ((logLogLower (n : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast (logLogLower_nonneg (n : ℚ) (by exact_mod_cast (show 1 ≤ n by omega)))
  have hn3q : 3 ≤ (n : ℚ) := by exact_mod_cast (by omega : 3 ≤ n)
  have hn2q : (n : ℚ) < 2 ^ logDepth := by
    have hn55440 : ((55440 : ℕ) : ℚ) < 2 ^ logDepth := by norm_num [logDepth]
    exact lt_of_le_of_lt (by exact_mod_cast hn2) hn55440
  have hll : ((logLogLower (n : ℚ) : ℚ) : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
    logLogLower_le_log_log (n : ℚ) hn3q hn2q
  have hnll0 : 0 ≤ (n : ℝ) * ((logLogLower (n : ℚ) : ℚ) : ℝ) :=
    mul_nonneg (by exact_mod_cast hnn) hll0
  calc
    (robinRhsLower n : ℝ)
        = (expGammaLowerQ : ℝ) * (n : ℝ) * ((logLogLower (n : ℚ) : ℚ) : ℝ) := by
          unfold robinRhsLower
          rw [Rat.cast_mul]
          rw [Rat.cast_mul]
          norm_num
    _ = (expGammaLowerQ : ℝ) * ((n : ℝ) * ((logLogLower (n : ℚ) : ℚ) : ℝ)) := by ring
    _ ≤ Real.exp Real.eulerMascheroniConstant * ((n : ℝ) * ((logLogLower (n : ℚ) : ℚ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right expGammaLowerQ_le_exp_gamma hnll0
    _ ≤ Real.exp Real.eulerMascheroniConstant * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
          have hE0 : 0 ≤ Real.exp Real.eulerMascheroniConstant := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hll (by exact_mod_cast hnn)) hE0
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring

/-! ## σ (divisor-sum) computed by pairing divisors around `√n` -/

private def sigmaSqrt (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0

private lemma divisors_filter_le_sqrt_eq (n : ℕ) (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ Nat.sqrt n) =
      (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d ∣ n) := by
  ext d
  by_cases hdpos : 0 < d
  · simp [Nat.mem_divisors, Finset.mem_filter, hn.ne']
    constructor
    · intro h
      exact ⟨⟨by omega, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  · have hd0 : d = 0 := by omega
    subst d
    simp [hn.ne']

private lemma large_divisors_sum_eq (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n), n / d := by
  refine Finset.sum_bij (fun d hd => n / d) ?hi ?hinj ?hsurj ?h
  · intro d hd
    have hdmem := (Finset.mem_filter.mp hd).1
    have hdgt := (Finset.mem_filter.mp hd).2
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdpos : 0 < d := by
      have : 0 ≤ Nat.sqrt n := Nat.zero_le _
      omega
    have hndvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
    have hndmem : n / d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    have hdecomp0 : n / d * d = n := Nat.div_mul_cancel hdvd
    have hdecomp : n = d * (n / d) := by
      simpa [mul_comm] using hdecomp0.symm
    have hndpos : 0 < n / d := by
      exact Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos
    have hnd_lt_d : n / d < d := by
      have hmain : n < d * d := by
        rw [← Nat.sqrt_lt]
        exact hdgt
      rw [hdecomp] at hmain
      exact (Nat.mul_lt_mul_left hdpos).mp hmain
    have hmul : n / d * (n / d) < n := by
      have h1 : n / d * (n / d) < n / d * d := by
        exact (Nat.mul_lt_mul_left hndpos).mpr hnd_lt_d
      simpa [hdecomp0] using h1
    have hnd_le_sqrt : n / d ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      exact le_of_lt hmul
    have hnd_nonsq : n / d * (n / d) ≠ n := by
      omega
    exact Finset.mem_filter.mpr ⟨hndmem, ⟨hnd_le_sqrt, hnd_nonsq⟩⟩
  · intro a ha b hb hab
    have hamem := (Finset.mem_filter.mp ha).1
    have hbmem := (Finset.mem_filter.mp hb).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hdiva : n / (n / a) = a := Nat.div_div_self hadvd (by omega)
    have hdivb : n / (n / b) = b := Nat.div_div_self hbdvd (by omega)
    calc
      a = n / (n / a) := hdiva.symm
      _ = n / (n / b) := by rw [hab]
      _ = b := hdivb
  · intro b hb
    have hbmem := (Finset.mem_filter.mp hb).1
    have hble := (Finset.mem_filter.mp hb).2.1
    have hbns := (Finset.mem_filter.mp hb).2.2
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hbpos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      subst b
      simp at hbdvd
      omega
    have hdpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
    have hdecomp0 : n / b * b = n := Nat.div_mul_cancel hbdvd
    have hdecomp : n = b * (n / b) := by
      simpa [mul_comm] using hdecomp0.symm
    have hb_le_sq : b * b ≤ n := by
      rw [Nat.le_sqrt] at hble
      exact hble
    have hb_sq_lt : b * b < n := lt_of_le_of_ne hb_le_sq hbns
    have hb_lt_nd : b < n / b := by
      rw [hdecomp] at hb_sq_lt
      exact (Nat.mul_lt_mul_left hbpos).mp hb_sq_lt
    have hndgt : Nat.sqrt n < n / b := by
      rw [Nat.sqrt_lt]
      have h1 : b * (n / b) < (n / b) * (n / b) := by
        exact (Nat.mul_lt_mul_right hdpos).mpr hb_lt_nd
      calc
        n = b * (n / b) := hdecomp
        _ < (n / b) * (n / b) := h1
    have hndvd : n / b ∣ n := Nat.div_dvd_of_dvd hbdvd
    have hndmem : n / b ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    refine ⟨n / b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hndmem, hndgt⟩
    · rw [Nat.div_div_self hbdvd (by omega)]
  · intro a ha
    have hamem := (Finset.mem_filter.mp ha).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    exact (Nat.div_div_self hadvd (by omega)).symm

private lemma sigma_eq_sigmaSqrt (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℕ) = sigmaSqrt n := by
  rw [ArithmeticFunction.sigma_one_apply]
  unfold sigmaSqrt
  let s : Finset ℕ := n.divisors.filter (fun d => d ≤ Nat.sqrt n)
  let t : Finset ℕ := n.divisors.filter (fun d => Nat.sqrt n < d)
  have hset := divisors_filter_le_sqrt_eq n hn
  have hsmall_final : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := by
    change (∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n), (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0
    rw [hset]
    rw [Finset.sum_filter]
  have hsplit_total : (∑ d ∈ n.divisors, d) =
      (∑ d ∈ s, d) + (∑ d ∈ t, d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ Nat.sqrt n) (f := fun d : ℕ => d)
    change (∑ d ∈ n.divisors, d) = (∑ d ∈ s, d) + (∑ d ∈ t, d)
    simpa [s, t, not_le] using h.symm
  have hsplit_small_id : (∑ d ∈ s, d) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => d)
    simpa using h.symm
  have hsplit_small_f : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => (if d * d = n then d else d + n / d))
    have hsq : (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d = n), d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d = n := (Finset.mem_filter.mp hd).2
      simp [hd']
    have hnsq : (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d ≠ n := (Finset.mem_filter.mp hd).2
      simp [hd']
    calc
      (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
          (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) := h.symm
      _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by rw [hsq, hnsq]
  have hlarge := large_divisors_sum_eq n hn
  have hlarge' : (∑ d ∈ t, d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d := by
    change (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d
    rw [hlarge]
    have hfilter : n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
        s.filter (fun d => d * d ≠ n) := by
      change n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
          (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).filter (fun d => d * d ≠ n)
      rw [Finset.filter_filter]
    rw [hfilter]
  calc
    ∑ d ∈ n.divisors, d = (∑ d ∈ s, d) + (∑ d ∈ t, d) := hsplit_total
    _ = ((∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), d)) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d) := by rw [hsplit_small_id, hlarge']
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          ((∑ d ∈ s.filter (fun d => d * d ≠ n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d)) := by omega
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ d ∈ s, (if d * d = n then d else d + n / d) := by
          rw [hsplit_small_f]
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := hsmall_final

/-! ## σ is bounded by `135000` throughout the range -/

set_option maxRecDepth 135000 in
private lemma sigma_le_135000_range (n : ℕ) (hL : 34541 ≤ n) (hU : n ≤ 35040) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 135000 := by
  have hn : 0 < n := by omega
  rw [sigma_eq_sigmaSqrt n hn]
  have hmem : n ∈ Finset.Icc 34541 35040 := Finset.mem_Icc.mpr ⟨hL, hU⟩
  have hcheck : ∀ k ∈ Finset.Icc 34541 35040, sigmaSqrt k ≤ 135000 := by
    intro k hk
    obtain ⟨hkL, hkU⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> decide +kernel
  exact hcheck n hmem

/-! ## the certified rational lower bound for the Robin RHS at `n = 34541` -/

set_option maxHeartbeats 0 in
private lemma robinRhsLower_34541_ge_135000 : ((135000 : ℕ) : ℚ) ≤ robinRhsLower 34541 := by
  unfold robinRhsLower logLogLower logLower logLowerAux logOneAddLower logOneAddV
    expGammaLowerQ gammaLowerQ expLower logTwoLowerQ logDepth
  decide +kernel

private lemma robin_rhs_34541_lower_bound :
    (135000 : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (34541 : ℝ) * Real.log (Real.log (34541 : ℝ)) := by
  have hq : ((135000 : ℕ) : ℝ) ≤ (robinRhsLower 34541 : ℝ) := by
    exact_mod_cast robinRhsLower_34541_ge_135000
  exact le_trans hq (robinRhsLower_le 34541 (by norm_num) (by norm_num))

/-! ## monotonicity of `e^γ · x · log (log x)` for `x ≥ 34541` -/

private lemma log_log_34541_nonneg : 0 ≤ Real.log (Real.log (34541 : ℝ)) := by
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (34541 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num : 0 < (34541 : ℝ))]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num : (3 : ℝ) ≤ (34541 : ℝ))
  exact Real.log_nonneg hlog_ge_one

private lemma log_log_mono_on_range (n : ℕ) (hL : 34541 ≤ n) :
    Real.log (Real.log (34541 : ℝ)) ≤ Real.log (Real.log (n : ℝ)) := by
  have h1 : (34541 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hL
  have hpos : 0 < (34541 : ℝ) := by norm_num
  have hlog_mono : Real.log (34541 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hpos h1
  have hlogpos : 0 < Real.log (34541 : ℝ) := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < (34541 : ℝ))
  exact Real.log_le_log hlogpos hlog_mono

private lemma robin_rhs_mono (n : ℕ) (hL : 34541 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * (34541 : ℝ) * Real.log (Real.log (34541 : ℝ)) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  have h34541 : (34541 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hL
  have hE : 0 ≤ Real.exp Real.eulerMascheroniConstant := (Real.exp_pos _).le
  have hll0 : 0 ≤ Real.log (Real.log (34541 : ℝ)) := log_log_34541_nonneg
  have hllm : Real.log (Real.log (34541 : ℝ)) ≤ Real.log (Real.log (n : ℝ)) :=
    log_log_mono_on_range n hL
  have hnm : (34541 : ℝ) * Real.log (Real.log (34541 : ℝ)) ≤
      (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
    exact mul_le_mul h34541 hllm hll0 (by positivity : 0 ≤ (n : ℝ))
  calc
    Real.exp Real.eulerMascheroniConstant * (34541 : ℝ) * Real.log (Real.log (34541 : ℝ))
        = Real.exp Real.eulerMascheroniConstant *
            ((34541 : ℝ) * Real.log (Real.log (34541 : ℝ))) := by ring
    _ ≤ Real.exp Real.eulerMascheroniConstant *
            ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hnm hE
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring

/-! ## assembly -/

/--
Robin's inequality `σ(n) ≤ e^γ · n · log log n` on the finite range `34541 ≤ n ≤ 35040`.
This is the finite check needed in Robin's criterion: `n = 5040` is the (only)
small counterexample, so any proof that the inequality holds for *all* `n ≥ 34541`
must in particular cover this range by direct computation.
-/
theorem finiteRange_34541_35040 (n : ℕ) (hL : 34541 ≤ n) (hU : n ≤ 35040) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  have hs : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (135000 : ℝ) := by
    exact_mod_cast sigma_le_135000_range n hL hU
  exact le_trans hs (le_trans robin_rhs_34541_lower_bound (robin_rhs_mono n hL))

end Commons.NumberTheory.Robin
