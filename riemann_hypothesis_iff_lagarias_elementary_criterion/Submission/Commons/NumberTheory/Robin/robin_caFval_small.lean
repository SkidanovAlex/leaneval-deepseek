import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Star
import Submission.Commons.NumberTheory.Robin.caMu_pos
import Submission.Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod
import Submission.Commons.NumberTheory.Robin.caSupp_eq_primesLE_xi
import Submission.Commons.NumberTheory.Robin.caSupp_nonempty_of_two_le
import Submission.Commons.NumberTheory.Robin.caF1_lt_one
import Submission.Commons.NumberTheory.Robin.caF1_le_inv_mul_log

open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! Certified rational lower/upper bounds for `log`, `exp` and Euler's constant γ,
    used to verify Robin's inequality on the finite range `5041 ≤ n ≤ 5100` by
    computation.  All the machinery below is `private`: it is module-local. -/

namespace Commons.NumberTheory.Robin

namespace RobinCaFval

def logOneAddV (t : ℚ) : ℚ := t / (2 + t)
private noncomputable def logOneAddVR (t : ℝ) : ℝ := t / (2 + t)

private noncomputable def logOneAddLowerR (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range 14, (logOneAddVR t) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

private noncomputable def logOneAddUpperR (t : ℝ) : ℝ :=
  2 * ((∑ i ∈ Finset.range 14, (logOneAddVR t) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
    (logOneAddVR t) ^ (2 * 14 + 1) / (1 - (logOneAddVR t) ^ 2))

def logOneAddLower (t : ℚ) : ℚ :=
  2 * (∑ i ∈ Finset.range 14, (logOneAddV t) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ))

def logOneAddUpper (t : ℚ) : ℚ :=
  2 * ((∑ i ∈ Finset.range 14, (logOneAddV t) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)) +
    (logOneAddV t) ^ (2 * 14 + 1) / (1 - (logOneAddV t) ^ 2))

def logTwoLowerQ : ℚ := 6931471803 / 10000000000
def logTwoUpperQ : ℚ := 6931471808 / 10000000000

def logDepth : ℕ := 13

def logLowerAux : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then logOneAddLower (x - 1) else 0
  | x, k + 1 =>
      if x < 2 then logOneAddLower (x - 1)
      else logTwoLowerQ + logLowerAux (x / 2) k

def logLower (x : ℚ) : ℚ := logLowerAux x logDepth

def logUpperAux : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then logOneAddUpper (x - 1) else 0
  | x, k + 1 =>
      if x < 2 then logOneAddUpper (x - 1)
      else logTwoUpperQ + logUpperAux (x / 2) k

def logUpper (x : ℚ) : ℚ := logUpperAux x logDepth

def expLower (x : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℚ)

def gammaLowerQ : ℚ := 23 / 40

def expGammaLowerQ : ℚ := expLower gammaLowerQ 24

def logLogLower (n : ℚ) : ℚ := logLower (max (logLower n) 1)

def robinRhsLower (n : ℕ) : ℚ :=
  expGammaLowerQ * (n : ℚ) * logLogLower (n : ℚ)

lemma logOneAddV_nonneg {t : ℚ} (ht : 0 ≤ t) : 0 ≤ logOneAddV t := by
  unfold logOneAddV
  positivity

lemma logOneAddV_lt_one {t : ℚ} (ht : 0 ≤ t) : logOneAddV t < 1 := by
  unfold logOneAddV
  have hden : 0 < 2 + t := by linarith
  rw [div_lt_one hden]
  linarith

lemma logOneAddVR_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logOneAddVR t := by
  unfold logOneAddVR
  positivity

lemma logOneAddVR_lt_one {t : ℝ} (ht : 0 ≤ t) : logOneAddVR t < 1 := by
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

lemma logOneAddLowerR_le_log_one_add (t : ℝ) (ht : 0 ≤ t) :
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

lemma logOneAddUpperR_ge_log_one_add (t : ℝ) (ht : 0 ≤ t) :
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

lemma logOneAddLower_cast (t : ℚ) :
    ((logOneAddLower t : ℚ) : ℝ) = logOneAddLowerR (t : ℝ) := by
  rw [logOneAddLower, logOneAddLowerR]
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  rw [Rat.cast_sum]
  simp only [Rat.cast_div, Rat.cast_pow, cast_v]
  norm_num

lemma logOneAddUpper_cast (t : ℚ) :
    ((logOneAddUpper t : ℚ) : ℝ) = logOneAddUpperR (t : ℝ) := by
  rw [logOneAddUpper, logOneAddUpperR]
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_sub]
  rw [Rat.cast_sum]
  simp only [Rat.cast_div, Rat.cast_pow, cast_v]
  norm_num
  rw [cast_v]

lemma logOneAddLower_le_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    ((logOneAddLower t : ℚ) : ℝ) ≤ Real.log (1 + (t : ℝ)) := by
  rw [logOneAddLower_cast]
  exact logOneAddLowerR_le_log_one_add (t : ℝ) (by exact_mod_cast ht)

lemma logOneAddUpper_ge_log_one_add (t : ℚ) (ht : 0 ≤ t) :
    Real.log (1 + (t : ℝ)) ≤ ((logOneAddUpper t : ℚ) : ℝ) := by
  rw [logOneAddUpper_cast]
  exact logOneAddUpperR_ge_log_one_add (t : ℝ) (by exact_mod_cast ht)

lemma logTwoLowerQ_le_log_two : ((logTwoLowerQ : ℚ) : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num [logTwoLowerQ] at h ⊢
  exact le_of_lt h

lemma logTwoUpperQ_ge_log_two : Real.log 2 ≤ ((logTwoUpperQ : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num [logTwoUpperQ] at h ⊢
  exact le_of_lt h

lemma logTwoLowerQ_nonneg : 0 ≤ logTwoLowerQ := by norm_num [logTwoLowerQ]
lemma logTwoUpperQ_nonneg : 0 ≤ logTwoUpperQ := by norm_num [logTwoUpperQ]

lemma logOneAddLower_nonneg (t : ℚ) (ht : 0 ≤ t) : 0 ≤ logOneAddLower t := by
  unfold logOneAddLower
  have hv : 0 ≤ logOneAddV t := logOneAddV_nonneg ht
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (pow_nonneg hv (2 * i + 1))
    (le_of_lt (by exact_mod_cast (show 0 < 2 * i + 1 by omega)))

lemma logOneAddUpper_nonneg (t : ℚ) (ht : 0 ≤ t) : 0 ≤ logOneAddUpper t := by
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

lemma logLowerAux_nonneg (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logLowerAux x k := by
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

lemma logUpperAux_nonneg (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logUpperAux x k := by
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

lemma logLowerAux_le_log (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ k) :
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

lemma logLower_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logLower x := by
  unfold logLower
  exact logLowerAux_nonneg logDepth x hx1

lemma logUpper_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logUpper x := by
  unfold logUpper
  exact logUpperAux_nonneg logDepth x hx1

lemma logLower_le_log (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    ((logLower x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  unfold logLower
  exact logLowerAux_le_log logDepth x hx1 hx

lemma logUpperAux_ge_log (k : ℕ) (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ k) :
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

lemma logUpper_ge_log (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    Real.log (x : ℝ) ≤ ((logUpper x : ℚ) : ℝ) := by
  unfold logUpper
  exact logUpperAux_ge_log logDepth x hx1 hx


private def roundUp10 (q : ℚ) : ℚ := (Rat.ceil (q * 10^10) : ℚ) / 10^10
private def roundDown10 (q : ℚ) : ℚ := (Rat.floor (q * 10^10) : ℚ) / 10^10
private def logUpperR (x : ℚ) : ℚ := roundUp10 (logUpper x)
private def logLowerR (x : ℚ) : ℚ := roundDown10 (logLower x)

private lemma le_roundUp10 (q : ℚ) : q ≤ roundUp10 q := by
  unfold roundUp10
  have h10 : (0:ℚ) < 10^10 := by norm_num
  rw [le_div_iff₀ h10]
  have := Rat.le_ceil (x := q * 10^10)
  linarith

private lemma roundDown10_le (q : ℚ) : roundDown10 q ≤ q := by
  unfold roundDown10
  have h10 : (0:ℚ) < 10^10 := by norm_num
  rw [div_le_iff₀ h10]
  have := Rat.floor_le (q * 10^10)
  linarith

private lemma log_le_logUpperR (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    Real.log (x : ℝ) ≤ ((logUpperR x : ℚ) : ℝ) := by
  have h1 := logUpper_ge_log x hx1 hx
  have h2 : ((logUpper x : ℚ) : ℝ) ≤ ((roundUp10 (logUpper x) : ℚ) : ℝ) := by
    exact_mod_cast le_roundUp10 (logUpper x)
  exact le_trans h1 (by simpa [logUpperR] using h2)

private lemma logLowerR_le_log (x : ℚ) (hx1 : 1 ≤ x) (hx : x < 2 ^ logDepth) :
    ((logLowerR x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  have h1 := logLower_le_log x hx1 hx
  have h2 : ((roundDown10 (logLower x) : ℚ) : ℝ) ≤ ((logLower x : ℚ) : ℝ) := by
    exact_mod_cast roundDown10_le (logLower x)
  exact le_trans (by simpa [logLowerR] using h2) h1

private lemma logUpperR_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logUpperR x := by
  have h1 := logUpper_nonneg x hx1
  have h2 := le_roundUp10 (logUpper x)
  simp only [logUpperR]; linarith

private lemma logLowerR_nonneg (x : ℚ) (hx1 : 1 ≤ x) : 0 ≤ logLowerR x := by
  have h1 := logLower_nonneg x hx1
  unfold logLowerR roundDown10
  have h2 : (0:ℚ) ≤ (Rat.floor (logLower x * 10^10) : ℚ) := by
    have h3 : (0:ℚ) ≤ logLower x * 10^10 := by positivity
    exact_mod_cast ((Int.floor_nonneg (a := logLower x * 10^10)).mpr h3)
  positivity

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

noncomputable def Fq (p k : ℕ) : ℝ := Real.log (((p:ℝ)^(k+1) - 1)/((p:ℝ)^(k+1) - (p:ℝ)))/Real.log (p:ℝ)
def rAq (p j : ℕ) : ℚ := (((p:ℚ)^(j+1) - 1)/((p:ℚ)^(j+1) - (p:ℚ)))

lemma cast_rAq (p j : ℕ) : ((rAq p j : ℚ) : ℝ) = (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) := by
  unfold rAq; push_cast; ring

lemma rAq_den_pos {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) : (0:ℚ) < (p:ℚ)^(j+1) - (p:ℚ) := by
  have hp1 : (1:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 1 < p)
  have hlt : (p:ℚ) < (p:ℚ)^(j+1) := by
    calc (p:ℚ) = (p:ℚ)^1 := (pow_one _).symm
      _ < (p:ℚ)^(j+1) := pow_lt_pow_right₀ hp1 (by omega)
  linarith

lemma rAq_ge_one {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) : (1:ℚ) ≤ rAq p j := by
  unfold rAq
  rw [le_div_iff₀ (rAq_den_pos hp hj)]
  have hp1 : (1:ℚ) ≤ (p:ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
  linarith

lemma rAq_lt_depth {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) : rAq p j < 2^logDepth := by
  have hlt2 : rAq p j < 2 := by
    unfold rAq
    rw [div_lt_iff₀ (rAq_den_pos hp hj)]
    have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp
    have hp1 : (1:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 1 < p)
    have hsq : (p:ℚ)^2 ≤ (p:ℚ)^(j+1) := by
      apply pow_le_pow_right₀ (le_of_lt hp1); omega
    nlinarith [hsq, hp2]
  calc rAq p j < 2 := hlt2
    _ < (2:ℚ)^logDepth := by norm_num [logDepth]

lemma Fq_num_pos {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) :
    0 < Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) := by
  apply Real.log_pos
  have hp1r : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hlt : (p:ℝ) < (p:ℝ)^(j+1) := by
    calc (p:ℝ) = (p:ℝ)^1 := (pow_one _).symm
      _ < (p:ℝ)^(j+1) := pow_lt_pow_right₀ hp1r (by omega)
  have hden : 0 < (p:ℝ)^(j+1) - (p:ℝ) := by linarith
  rw [one_lt_div hden]
  linarith

lemma F1_le_F_of {q p j : ℕ} (hq : 2 ≤ q) (hp : 2 ≤ p) (hj : 1 ≤ j)
    (hqLt : q < 2^logDepth) (hpLt : p < 2^logDepth)
    (h : logUpper (((q:ℚ)+1)/(q:ℚ)) * logUpper (p:ℚ) ≤ logLower (rAq p j) * logLower (q:ℚ)) :
    Fq q 1 ≤ Fq p j := by
  have hq1r : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hp1r : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos hq1r
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos hp1r
  have hnum_pos : 0 < Real.log (((q:ℝ)+1)/(q:ℝ)) := by
    apply Real.log_pos; rw [one_lt_div hq0]; linarith
  have hApos := Fq_num_pos hp hj
  have hq2q : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq
  have hqposq : (0:ℚ) < (q:ℚ) := by linarith
  have hq1q : (1:ℚ) ≤ ((q:ℚ)+1)/(q:ℚ) := by rw [le_div_iff₀ hqposq]; linarith
  have hqlt : ((q:ℚ)+1)/(q:ℚ) < 2^logDepth := by
    have h2 : ((q:ℚ)+1)/(q:ℚ) ≤ 2 := by rw [div_le_iff₀ hqposq]; linarith
    calc ((q:ℚ)+1)/(q:ℚ) ≤ 2 := h2
      _ < (2:ℚ)^logDepth := by norm_num [logDepth]
  have hpq1 : (1:ℚ) ≤ (p:ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hplt : (p:ℚ) < 2^logDepth := by exact_mod_cast hpLt
  have hq1q' : (1:ℚ) ≤ (q:ℚ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlt' : (q:ℚ) < 2^logDepth := by exact_mod_cast hqLt
  have U1 := logUpper_ge_log (((q:ℚ)+1)/(q:ℚ)) hq1q hqlt
  have U2 := logUpper_ge_log (p:ℚ) hpq1 hplt
  have L1 := logLower_le_log (rAq p j) (rAq_ge_one hp hj) (rAq_lt_depth hp hj)
  have L2 := logLower_le_log (q:ℚ) hq1q' hqlt'
  have hL1' : ((logLower (rAq p j) : ℚ) : ℝ) ≤ Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) := by
    simpa [cast_rAq] using L1
  have hU1' : Real.log (((q:ℝ)+1)/(q:ℝ)) ≤ ((logUpper (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) := by
    have hc : ((((q:ℚ)+1)/(q:ℚ) : ℚ) : ℝ) = ((q:ℝ)+1)/(q:ℝ) := by push_cast; ring
    simpa [hc] using U1
  have hmul : Real.log (((q:ℝ)+1)/(q:ℝ)) * Real.log (p:ℝ)
      ≤ (((logUpper (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) * ((logUpper (p:ℚ) : ℚ) : ℝ)) := by
    have hb : (0:ℝ) ≤ ((logUpper (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast (logUpper_nonneg (((q:ℚ)+1)/(q:ℚ)) hq1q)
    exact mul_le_mul hU1' U2 (le_of_lt hlogp) hb
  have hmul2 : (((logLower (rAq p j) : ℚ) : ℝ) * ((logLower (q:ℚ) : ℚ) : ℝ))
      ≤ Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) * Real.log (q:ℝ) := by
    have hb : (0:ℝ) ≤ ((logLower (q:ℚ) : ℚ) : ℝ) := by
      exact_mod_cast (logLower_nonneg (q:ℚ) hq1q')
    exact mul_le_mul hL1' L2 hb (le_of_lt hApos)
  have hh : (((logUpper (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) * ((logUpper (p:ℚ) : ℚ) : ℝ))
      ≤ (((logLower (rAq p j) : ℚ) : ℝ) * ((logLower (q:ℚ) : ℚ) : ℝ)) := by
    exact_mod_cast h
  have hkey : Real.log (((q:ℝ)+1)/(q:ℝ)) * Real.log (p:ℝ)
      ≤ Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) * Real.log (q:ℝ) :=
    le_trans (le_trans hmul hh) hmul2
  have hnum_eq : (((q:ℝ)^(1+1)-1)/((q:ℝ)^(1+1)-(q:ℝ))) = ((q:ℝ)+1)/(q:ℝ) := by
    have h1 : (q:ℝ) ≠ 0 := ne_of_gt hq0
    have h2 : (q:ℝ) - 1 ≠ 0 := by linarith
    have h3 : (q:ℝ)^2 - (q:ℝ) ≠ 0 := by
      have : (q:ℝ)^2 - (q:ℝ) = (q:ℝ)*((q:ℝ)-1) := by ring
      rw [this]; exact mul_ne_zero h1 h2
    field_simp
    ring
  unfold Fq
  rw [hnum_eq, div_le_div_iff₀ hlogq hlogp]
  linarith [hkey]

lemma F1_gt_F_of {q p j : ℕ} (hq : 2 ≤ q) (hp : 2 ≤ p) (hj : 1 ≤ j)
    (hqLt : q < 2^logDepth) (hpLt : p < 2^logDepth)
    (h : logUpper (rAq p j) * logUpper (q:ℚ) < logLower (((q:ℚ)+1)/(q:ℚ)) * logLower (p:ℚ)) :
    Fq p j < Fq q 1 := by
  have hq1r : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hp1r : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos hq1r
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos hp1r
  have hnum_pos : 0 < Real.log (((q:ℝ)+1)/(q:ℝ)) := by
    apply Real.log_pos; rw [one_lt_div hq0]; linarith
  have hApos := Fq_num_pos hp hj
  have hqposq : (0:ℚ) < (q:ℚ) := by exact_mod_cast (by omega : 0 < q)
  have hq2q : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq
  have hq1q : (1:ℚ) ≤ ((q:ℚ)+1)/(q:ℚ) := by rw [le_div_iff₀ hqposq]; linarith
  have hqlt : ((q:ℚ)+1)/(q:ℚ) < 2^logDepth := by
    have h2 : ((q:ℚ)+1)/(q:ℚ) ≤ 2 := by rw [div_le_iff₀ hqposq]; linarith
    calc ((q:ℚ)+1)/(q:ℚ) ≤ 2 := h2
      _ < (2:ℚ)^logDepth := by norm_num [logDepth]
  have hpq1 : (1:ℚ) ≤ (p:ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hplt : (p:ℚ) < 2^logDepth := by exact_mod_cast hpLt
  have hq1q' : (1:ℚ) ≤ (q:ℚ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlt' : (q:ℚ) < 2^logDepth := by exact_mod_cast hqLt
  have U1 := logUpper_ge_log (rAq p j) (rAq_ge_one hp hj) (rAq_lt_depth hp hj)
  have U2 := logUpper_ge_log (q:ℚ) hq1q' hqlt'
  have L1 := logLower_le_log (((q:ℚ)+1)/(q:ℚ)) hq1q hqlt
  have L2 := logLower_le_log (p:ℚ) hpq1 hplt
  have hU2' : Real.log (q:ℝ) ≤ ((logUpper (q:ℚ) : ℚ) : ℝ) := U2
  have hU1' : Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) ≤ ((logUpper (rAq p j) : ℚ) : ℝ) := by
    have hc := cast_rAq p j
    rw [hc] at U1; exact U1
  have hL1' : ((logLower (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) ≤ Real.log (((q:ℝ)+1)/(q:ℝ)) := by
    have hc : ((((q:ℚ)+1)/(q:ℚ) : ℚ) : ℝ) = ((q:ℝ)+1)/(q:ℝ) := by push_cast; ring
    simpa [hc] using L1
  have hL2' : ((logLower (p:ℚ) : ℚ) : ℝ) ≤ Real.log (p:ℝ) := L2
  have hUprod : Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) * Real.log (q:ℝ)
      ≤ (((logUpper (rAq p j) : ℚ) : ℝ) * ((logUpper (q:ℚ) : ℚ) : ℝ)) := by
    have hb : (0:ℝ) ≤ ((logUpper (rAq p j) : ℚ) : ℝ) := by
      exact_mod_cast (logUpper_nonneg (rAq p j) (rAq_ge_one hp hj))
    exact mul_le_mul hU1' hU2' (le_of_lt hlogq) hb
  have hLprod : (((logLower (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) * ((logLower (p:ℚ) : ℚ) : ℝ))
      ≤ Real.log (((q:ℝ)+1)/(q:ℝ)) * Real.log (p:ℝ) := by
    have hb : (0:ℝ) ≤ ((logLower (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast (logLower_nonneg (((q:ℚ)+1)/(q:ℚ)) hq1q)
    have hb2 : (0:ℝ) ≤ ((logLower (p:ℚ) : ℚ) : ℝ) := by
      exact_mod_cast (logLower_nonneg (p:ℚ) hpq1)
    exact mul_le_mul hL1' hL2' hb2 (le_of_lt hnum_pos)
  have hh : (((logUpper (rAq p j) : ℚ) : ℝ) * ((logUpper (q:ℚ) : ℚ) : ℝ))
      < (((logLower (((q:ℚ)+1)/(q:ℚ)) : ℚ) : ℝ) * ((logLower (p:ℚ) : ℚ) : ℝ)) := by
    exact_mod_cast h
  have hkey : Real.log (((p:ℝ)^(j+1) - 1)/((p:ℝ)^(j+1) - (p:ℝ))) * Real.log (q:ℝ)
      < Real.log (((q:ℝ)+1)/(q:ℝ)) * Real.log (p:ℝ) :=
    lt_of_le_of_lt hUprod (lt_of_lt_of_le hh hLprod)
  have hnum_eq : (((q:ℝ)^(1+1)-1)/((q:ℝ)^(1+1)-(q:ℝ))) = ((q:ℝ)+1)/(q:ℝ) := by
    have h1 : (q:ℝ) ≠ 0 := ne_of_gt hq0
    have h2 : (q:ℝ) - 1 ≠ 0 := by linarith
    have h3 : (q:ℝ)^2 - (q:ℝ) ≠ 0 := by
      have : (q:ℝ)^2 - (q:ℝ) = (q:ℝ)*((q:ℝ)-1) := by ring
      rw [this]; exact mul_ne_zero h1 h2
    field_simp
    ring
  unfold Fq
  rw [hnum_eq, div_lt_div_iff₀ hlogp hlogq]
  linarith [hkey]





lemma Fq_pos (p : ℕ) (hp : 2 ≤ p) : 0 < Fq p 1 := by
  have hp1r : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hden : (0:ℝ) < (p:ℝ)^(1+1) - (p:ℝ) := by
    have h2 : (p:ℝ)^(1+1) = (p:ℝ)^2 := by norm_num
    rw [h2]; nlinarith [hp0, hp1r]
  have hnum : 1 < (((p:ℝ)^(1+1) - 1) / ((p:ℝ)^(1+1) - (p:ℝ))) := by
    rw [one_lt_div hden]
    have h2 : (p:ℝ)^(1+1) = (p:ℝ)^2 := by norm_num
    rw [h2]; nlinarith [hp1r]
  unfold Fq
  exact div_pos (Real.log_pos hnum) (Real.log_pos hp1r)


lemma Fq_eq (p : ℕ) (hp : 2 ≤ p) : Fq p 1 = Real.log (1 + 1/(p:ℝ))/Real.log (p:ℝ) := by
  unfold Fq
  have h3 : (p:ℝ)^(1+1) = (p:ℝ)^2 := by norm_num
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpne0 : (p:ℝ) ≠ 0 := by positivity
  have hpne : (p:ℝ) - 1 ≠ 0 := by linarith
  have heq : (((p:ℝ)^(1+1)-1)/((p:ℝ)^(1+1)-(p:ℝ))) = 1 + 1/(p:ℝ) := by
    rw [h3]; field_simp; ring
  rw [heq]

lemma Fq_mono {q ξ : ℕ} (hq : 2 ≤ q) (hξ : 2 ≤ ξ) (hle : q ≤ ξ) : Fq ξ 1 ≤ Fq q 1 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
    have hξ1 : (1:ℝ) < (ξ:ℝ) := by exact_mod_cast (by omega : 1 < ξ)
    have h := Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
      (show (q:ℝ) ∈ Set.Ioi 1 from hq1) (show (ξ:ℝ) ∈ Set.Ioi 1 from hξ1)
      (by exact_mod_cast hlt)
    rw [Fq_eq q hq, Fq_eq ξ hξ]
    exact le_of_lt h
  · subst heq; rfl

noncomputable def muF (p : ℕ) (ε : ℝ) : ℝ := Real.log ((((p:ℝ)^(1+ε)) - 1) / (((p:ℝ)^(1+ε)) - (p:ℝ))) / Real.log (p:ℝ)
def rq (p K : ℕ) : ℚ := (((p:ℚ)^(K+1) - 1) / ((p:ℚ)^K * ((p:ℚ)-1)))
def plist : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523]
def pfs (ξ : ℕ) : Finset ℕ := plist.toFinset.filter (fun p => p ≤ ξ)
def thrJ : ℕ → Finset ℕ := fun p =>

  if p = 2 then Finset.Icc 2 12 else
  if p = 3 then Finset.Icc 2 8 else
  if p = 5 then Finset.Icc 2 5 else
  if p = 7 then Finset.Icc 2 4 else
  if p = 11 then Finset.Icc 2 3 else
  if p = 13 then Finset.Icc 2 3 else
  if p = 17 then Finset.Icc 2 2 else
  if p = 19 then Finset.Icc 2 2 else
  if p = 23 then Finset.Icc 2 2 else
  if p = 29 then Finset.Icc 2 2 else
  if p = 31 then Finset.Icc 2 2 else
  if p = 37 then Finset.Icc 2 2 else
  if p = 41 then Finset.Icc 2 2 else
  if p = 43 then Finset.Icc 2 2 else
  if p = 47 then Finset.Icc 2 2 else
  ∅


def thrJmax : ℕ → ℕ
  | 2 => 12
  | 3 => 8
  | 5 => 5
  | 7 => 4
  | 11 => 3
  | 13 => 3
  | 17 => 2
  | 19 => 2
  | 23 => 2
  | 29 => 2
  | 31 => 2
  | 37 => 2
  | 41 => 2
  | 43 => 2
  | 47 => 2
  | _ => 1

def thrV : ℕ → ℕ → ℕ

  | 2, 2 => 5

  | 2, 3 => 7

  | 2, 4 => 11

  | 2, 5 => 17

  | 2, 6 => 29

  | 2, 7 => 47

  | 2, 8 => 83

  | 2, 9 => 149

  | 2, 10 => 257

  | 2, 11 => 463

  | 2, 12 => 853

  | 3, 2 => 7

  | 3, 3 => 17

  | 3, 4 => 37

  | 3, 5 => 89

  | 3, 6 => 223

  | 3, 7 => 569

  | 3, 8 => 1481

  | 5, 2 => 17

  | 5, 3 => 61

  | 5, 4 => 233

  | 5, 5 => 929

  | 7, 2 => 37

  | 7, 3 => 157

  | 7, 4 => 821

  | 11, 2 => 79

  | 11, 3 => 557

  | 13, 2 => 101

  | 13, 3 => 907

  | 17, 2 => 173

  | 19, 2 => 211

  | 23, 2 => 307

  | 29, 2 => 479

  | 31, 2 => 547

  | 37, 2 => 769

  | 41, 2 => 937

  | 43, 2 => 1031

  | 47, 2 => 1223

  | _, _ => 0

def thrPrev : ℕ → ℕ → ℕ

  | 2, 2 => 3

  | 2, 3 => 5

  | 2, 4 => 7

  | 2, 5 => 13

  | 2, 6 => 23

  | 2, 7 => 43

  | 2, 8 => 79

  | 2, 9 => 139

  | 2, 10 => 251

  | 2, 11 => 461

  | 2, 12 => 839

  | 3, 2 => 5

  | 3, 3 => 13

  | 3, 4 => 31

  | 3, 5 => 83

  | 3, 6 => 211

  | 3, 7 => 563

  | 3, 8 => 1471

  | 5, 2 => 13

  | 5, 3 => 59

  | 5, 4 => 229

  | 5, 5 => 919

  | 7, 2 => 31

  | 7, 3 => 151

  | 7, 4 => 811

  | 11, 2 => 73

  | 11, 3 => 547

  | 13, 2 => 97

  | 13, 3 => 887

  | 17, 2 => 167

  | 19, 2 => 199

  | 23, 2 => 293

  | 29, 2 => 467

  | 31, 2 => 541

  | 37, 2 => 761

  | 41, 2 => 929

  | 43, 2 => 1021

  | 47, 2 => 1217

  | _, _ => 0


def thrSet (ξ p : ℕ) : Finset ℕ := (thrJ p).filter (fun j => thrV p j ≤ ξ)
def kminC (ξ p : ℕ) : ℕ := if h : (thrSet ξ p).Nonempty then (thrSet ξ p).max' h else 1
def kmaxC (ξnext p : ℕ) : ℕ := if h : (thrSet ξnext p).Nonempty then (thrSet ξnext p).max' h else 1
def LHSq (ξ ξnext : ℕ) : ℚ := ∑ p ∈ pfs ξ, logUpper (rq p (kmaxC ξnext p))
def ellq (ξ : ℕ) : ℚ := ∑ p ∈ pfs ξ, (kminC ξ p : ℚ) * logLower (p:ℚ)
def RHSq (ξ : ℕ) : ℚ := logLower (max (logLower (ellq ξ)) 1)

lemma thrJ_eq_2 : thrJ 2 = Finset.Icc 2 12 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (2:ℕ) ≠ 3)]
  rw [if_neg (by decide : (2:ℕ) ≠ 5)]
  rw [if_neg (by decide : (2:ℕ) ≠ 7)]
  rw [if_neg (by decide : (2:ℕ) ≠ 11)]
  rw [if_neg (by decide : (2:ℕ) ≠ 13)]
  rw [if_neg (by decide : (2:ℕ) ≠ 17)]
  rw [if_neg (by decide : (2:ℕ) ≠ 19)]
  rw [if_neg (by decide : (2:ℕ) ≠ 23)]
  rw [if_neg (by decide : (2:ℕ) ≠ 29)]
  rw [if_neg (by decide : (2:ℕ) ≠ 31)]
  rw [if_neg (by decide : (2:ℕ) ≠ 37)]
  rw [if_neg (by decide : (2:ℕ) ≠ 41)]
  rw [if_neg (by decide : (2:ℕ) ≠ 43)]
  rw [if_neg (by decide : (2:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_3 : thrJ 3 = Finset.Icc 2 8 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (3:ℕ) ≠ 2)]
  rw [if_neg (by decide : (3:ℕ) ≠ 5)]
  rw [if_neg (by decide : (3:ℕ) ≠ 7)]
  rw [if_neg (by decide : (3:ℕ) ≠ 11)]
  rw [if_neg (by decide : (3:ℕ) ≠ 13)]
  rw [if_neg (by decide : (3:ℕ) ≠ 17)]
  rw [if_neg (by decide : (3:ℕ) ≠ 19)]
  rw [if_neg (by decide : (3:ℕ) ≠ 23)]
  rw [if_neg (by decide : (3:ℕ) ≠ 29)]
  rw [if_neg (by decide : (3:ℕ) ≠ 31)]
  rw [if_neg (by decide : (3:ℕ) ≠ 37)]
  rw [if_neg (by decide : (3:ℕ) ≠ 41)]
  rw [if_neg (by decide : (3:ℕ) ≠ 43)]
  rw [if_neg (by decide : (3:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_5 : thrJ 5 = Finset.Icc 2 5 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (5:ℕ) ≠ 2)]
  rw [if_neg (by decide : (5:ℕ) ≠ 3)]
  rw [if_neg (by decide : (5:ℕ) ≠ 7)]
  rw [if_neg (by decide : (5:ℕ) ≠ 11)]
  rw [if_neg (by decide : (5:ℕ) ≠ 13)]
  rw [if_neg (by decide : (5:ℕ) ≠ 17)]
  rw [if_neg (by decide : (5:ℕ) ≠ 19)]
  rw [if_neg (by decide : (5:ℕ) ≠ 23)]
  rw [if_neg (by decide : (5:ℕ) ≠ 29)]
  rw [if_neg (by decide : (5:ℕ) ≠ 31)]
  rw [if_neg (by decide : (5:ℕ) ≠ 37)]
  rw [if_neg (by decide : (5:ℕ) ≠ 41)]
  rw [if_neg (by decide : (5:ℕ) ≠ 43)]
  rw [if_neg (by decide : (5:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_7 : thrJ 7 = Finset.Icc 2 4 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (7:ℕ) ≠ 2)]
  rw [if_neg (by decide : (7:ℕ) ≠ 3)]
  rw [if_neg (by decide : (7:ℕ) ≠ 5)]
  rw [if_neg (by decide : (7:ℕ) ≠ 11)]
  rw [if_neg (by decide : (7:ℕ) ≠ 13)]
  rw [if_neg (by decide : (7:ℕ) ≠ 17)]
  rw [if_neg (by decide : (7:ℕ) ≠ 19)]
  rw [if_neg (by decide : (7:ℕ) ≠ 23)]
  rw [if_neg (by decide : (7:ℕ) ≠ 29)]
  rw [if_neg (by decide : (7:ℕ) ≠ 31)]
  rw [if_neg (by decide : (7:ℕ) ≠ 37)]
  rw [if_neg (by decide : (7:ℕ) ≠ 41)]
  rw [if_neg (by decide : (7:ℕ) ≠ 43)]
  rw [if_neg (by decide : (7:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_11 : thrJ 11 = Finset.Icc 2 3 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (11:ℕ) ≠ 2)]
  rw [if_neg (by decide : (11:ℕ) ≠ 3)]
  rw [if_neg (by decide : (11:ℕ) ≠ 5)]
  rw [if_neg (by decide : (11:ℕ) ≠ 7)]
  rw [if_neg (by decide : (11:ℕ) ≠ 13)]
  rw [if_neg (by decide : (11:ℕ) ≠ 17)]
  rw [if_neg (by decide : (11:ℕ) ≠ 19)]
  rw [if_neg (by decide : (11:ℕ) ≠ 23)]
  rw [if_neg (by decide : (11:ℕ) ≠ 29)]
  rw [if_neg (by decide : (11:ℕ) ≠ 31)]
  rw [if_neg (by decide : (11:ℕ) ≠ 37)]
  rw [if_neg (by decide : (11:ℕ) ≠ 41)]
  rw [if_neg (by decide : (11:ℕ) ≠ 43)]
  rw [if_neg (by decide : (11:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_13 : thrJ 13 = Finset.Icc 2 3 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (13:ℕ) ≠ 2)]
  rw [if_neg (by decide : (13:ℕ) ≠ 3)]
  rw [if_neg (by decide : (13:ℕ) ≠ 5)]
  rw [if_neg (by decide : (13:ℕ) ≠ 7)]
  rw [if_neg (by decide : (13:ℕ) ≠ 11)]
  rw [if_neg (by decide : (13:ℕ) ≠ 17)]
  rw [if_neg (by decide : (13:ℕ) ≠ 19)]
  rw [if_neg (by decide : (13:ℕ) ≠ 23)]
  rw [if_neg (by decide : (13:ℕ) ≠ 29)]
  rw [if_neg (by decide : (13:ℕ) ≠ 31)]
  rw [if_neg (by decide : (13:ℕ) ≠ 37)]
  rw [if_neg (by decide : (13:ℕ) ≠ 41)]
  rw [if_neg (by decide : (13:ℕ) ≠ 43)]
  rw [if_neg (by decide : (13:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_17 : thrJ 17 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (17:ℕ) ≠ 2)]
  rw [if_neg (by decide : (17:ℕ) ≠ 3)]
  rw [if_neg (by decide : (17:ℕ) ≠ 5)]
  rw [if_neg (by decide : (17:ℕ) ≠ 7)]
  rw [if_neg (by decide : (17:ℕ) ≠ 11)]
  rw [if_neg (by decide : (17:ℕ) ≠ 13)]
  rw [if_neg (by decide : (17:ℕ) ≠ 19)]
  rw [if_neg (by decide : (17:ℕ) ≠ 23)]
  rw [if_neg (by decide : (17:ℕ) ≠ 29)]
  rw [if_neg (by decide : (17:ℕ) ≠ 31)]
  rw [if_neg (by decide : (17:ℕ) ≠ 37)]
  rw [if_neg (by decide : (17:ℕ) ≠ 41)]
  rw [if_neg (by decide : (17:ℕ) ≠ 43)]
  rw [if_neg (by decide : (17:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_19 : thrJ 19 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (19:ℕ) ≠ 2)]
  rw [if_neg (by decide : (19:ℕ) ≠ 3)]
  rw [if_neg (by decide : (19:ℕ) ≠ 5)]
  rw [if_neg (by decide : (19:ℕ) ≠ 7)]
  rw [if_neg (by decide : (19:ℕ) ≠ 11)]
  rw [if_neg (by decide : (19:ℕ) ≠ 13)]
  rw [if_neg (by decide : (19:ℕ) ≠ 17)]
  rw [if_neg (by decide : (19:ℕ) ≠ 23)]
  rw [if_neg (by decide : (19:ℕ) ≠ 29)]
  rw [if_neg (by decide : (19:ℕ) ≠ 31)]
  rw [if_neg (by decide : (19:ℕ) ≠ 37)]
  rw [if_neg (by decide : (19:ℕ) ≠ 41)]
  rw [if_neg (by decide : (19:ℕ) ≠ 43)]
  rw [if_neg (by decide : (19:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_23 : thrJ 23 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (23:ℕ) ≠ 2)]
  rw [if_neg (by decide : (23:ℕ) ≠ 3)]
  rw [if_neg (by decide : (23:ℕ) ≠ 5)]
  rw [if_neg (by decide : (23:ℕ) ≠ 7)]
  rw [if_neg (by decide : (23:ℕ) ≠ 11)]
  rw [if_neg (by decide : (23:ℕ) ≠ 13)]
  rw [if_neg (by decide : (23:ℕ) ≠ 17)]
  rw [if_neg (by decide : (23:ℕ) ≠ 19)]
  rw [if_neg (by decide : (23:ℕ) ≠ 29)]
  rw [if_neg (by decide : (23:ℕ) ≠ 31)]
  rw [if_neg (by decide : (23:ℕ) ≠ 37)]
  rw [if_neg (by decide : (23:ℕ) ≠ 41)]
  rw [if_neg (by decide : (23:ℕ) ≠ 43)]
  rw [if_neg (by decide : (23:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_29 : thrJ 29 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (29:ℕ) ≠ 2)]
  rw [if_neg (by decide : (29:ℕ) ≠ 3)]
  rw [if_neg (by decide : (29:ℕ) ≠ 5)]
  rw [if_neg (by decide : (29:ℕ) ≠ 7)]
  rw [if_neg (by decide : (29:ℕ) ≠ 11)]
  rw [if_neg (by decide : (29:ℕ) ≠ 13)]
  rw [if_neg (by decide : (29:ℕ) ≠ 17)]
  rw [if_neg (by decide : (29:ℕ) ≠ 19)]
  rw [if_neg (by decide : (29:ℕ) ≠ 23)]
  rw [if_neg (by decide : (29:ℕ) ≠ 31)]
  rw [if_neg (by decide : (29:ℕ) ≠ 37)]
  rw [if_neg (by decide : (29:ℕ) ≠ 41)]
  rw [if_neg (by decide : (29:ℕ) ≠ 43)]
  rw [if_neg (by decide : (29:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_31 : thrJ 31 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (31:ℕ) ≠ 2)]
  rw [if_neg (by decide : (31:ℕ) ≠ 3)]
  rw [if_neg (by decide : (31:ℕ) ≠ 5)]
  rw [if_neg (by decide : (31:ℕ) ≠ 7)]
  rw [if_neg (by decide : (31:ℕ) ≠ 11)]
  rw [if_neg (by decide : (31:ℕ) ≠ 13)]
  rw [if_neg (by decide : (31:ℕ) ≠ 17)]
  rw [if_neg (by decide : (31:ℕ) ≠ 19)]
  rw [if_neg (by decide : (31:ℕ) ≠ 23)]
  rw [if_neg (by decide : (31:ℕ) ≠ 29)]
  rw [if_neg (by decide : (31:ℕ) ≠ 37)]
  rw [if_neg (by decide : (31:ℕ) ≠ 41)]
  rw [if_neg (by decide : (31:ℕ) ≠ 43)]
  rw [if_neg (by decide : (31:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_37 : thrJ 37 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (37:ℕ) ≠ 2)]
  rw [if_neg (by decide : (37:ℕ) ≠ 3)]
  rw [if_neg (by decide : (37:ℕ) ≠ 5)]
  rw [if_neg (by decide : (37:ℕ) ≠ 7)]
  rw [if_neg (by decide : (37:ℕ) ≠ 11)]
  rw [if_neg (by decide : (37:ℕ) ≠ 13)]
  rw [if_neg (by decide : (37:ℕ) ≠ 17)]
  rw [if_neg (by decide : (37:ℕ) ≠ 19)]
  rw [if_neg (by decide : (37:ℕ) ≠ 23)]
  rw [if_neg (by decide : (37:ℕ) ≠ 29)]
  rw [if_neg (by decide : (37:ℕ) ≠ 31)]
  rw [if_neg (by decide : (37:ℕ) ≠ 41)]
  rw [if_neg (by decide : (37:ℕ) ≠ 43)]
  rw [if_neg (by decide : (37:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_41 : thrJ 41 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (41:ℕ) ≠ 2)]
  rw [if_neg (by decide : (41:ℕ) ≠ 3)]
  rw [if_neg (by decide : (41:ℕ) ≠ 5)]
  rw [if_neg (by decide : (41:ℕ) ≠ 7)]
  rw [if_neg (by decide : (41:ℕ) ≠ 11)]
  rw [if_neg (by decide : (41:ℕ) ≠ 13)]
  rw [if_neg (by decide : (41:ℕ) ≠ 17)]
  rw [if_neg (by decide : (41:ℕ) ≠ 19)]
  rw [if_neg (by decide : (41:ℕ) ≠ 23)]
  rw [if_neg (by decide : (41:ℕ) ≠ 29)]
  rw [if_neg (by decide : (41:ℕ) ≠ 31)]
  rw [if_neg (by decide : (41:ℕ) ≠ 37)]
  rw [if_neg (by decide : (41:ℕ) ≠ 43)]
  rw [if_neg (by decide : (41:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_43 : thrJ 43 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (43:ℕ) ≠ 2)]
  rw [if_neg (by decide : (43:ℕ) ≠ 3)]
  rw [if_neg (by decide : (43:ℕ) ≠ 5)]
  rw [if_neg (by decide : (43:ℕ) ≠ 7)]
  rw [if_neg (by decide : (43:ℕ) ≠ 11)]
  rw [if_neg (by decide : (43:ℕ) ≠ 13)]
  rw [if_neg (by decide : (43:ℕ) ≠ 17)]
  rw [if_neg (by decide : (43:ℕ) ≠ 19)]
  rw [if_neg (by decide : (43:ℕ) ≠ 23)]
  rw [if_neg (by decide : (43:ℕ) ≠ 29)]
  rw [if_neg (by decide : (43:ℕ) ≠ 31)]
  rw [if_neg (by decide : (43:ℕ) ≠ 37)]
  rw [if_neg (by decide : (43:ℕ) ≠ 41)]
  rw [if_neg (by decide : (43:ℕ) ≠ 47)]
  rw [if_pos rfl]

lemma thrJ_eq_47 : thrJ 47 = Finset.Icc 2 2 := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (47:ℕ) ≠ 2)]
  rw [if_neg (by decide : (47:ℕ) ≠ 3)]
  rw [if_neg (by decide : (47:ℕ) ≠ 5)]
  rw [if_neg (by decide : (47:ℕ) ≠ 7)]
  rw [if_neg (by decide : (47:ℕ) ≠ 11)]
  rw [if_neg (by decide : (47:ℕ) ≠ 13)]
  rw [if_neg (by decide : (47:ℕ) ≠ 17)]
  rw [if_neg (by decide : (47:ℕ) ≠ 19)]
  rw [if_neg (by decide : (47:ℕ) ≠ 23)]
  rw [if_neg (by decide : (47:ℕ) ≠ 29)]
  rw [if_neg (by decide : (47:ℕ) ≠ 31)]
  rw [if_neg (by decide : (47:ℕ) ≠ 37)]
  rw [if_neg (by decide : (47:ℕ) ≠ 41)]
  rw [if_neg (by decide : (47:ℕ) ≠ 43)]
  rw [if_pos rfl]

lemma thrJ_eq_empty_of_ge : ∀ (p : ℕ), 48 ≤ p → thrJ p = ∅ := by
  intro p hp
  dsimp only [thrJ]
  rw [if_neg (by omega : (p:ℕ) ≠ 2)]
  rw [if_neg (by omega : (p:ℕ) ≠ 3)]
  rw [if_neg (by omega : (p:ℕ) ≠ 5)]
  rw [if_neg (by omega : (p:ℕ) ≠ 7)]
  rw [if_neg (by omega : (p:ℕ) ≠ 11)]
  rw [if_neg (by omega : (p:ℕ) ≠ 13)]
  rw [if_neg (by omega : (p:ℕ) ≠ 17)]
  rw [if_neg (by omega : (p:ℕ) ≠ 19)]
  rw [if_neg (by omega : (p:ℕ) ≠ 23)]
  rw [if_neg (by omega : (p:ℕ) ≠ 29)]
  rw [if_neg (by omega : (p:ℕ) ≠ 31)]
  rw [if_neg (by omega : (p:ℕ) ≠ 37)]
  rw [if_neg (by omega : (p:ℕ) ≠ 41)]
  rw [if_neg (by omega : (p:ℕ) ≠ 43)]
  rw [if_neg (by omega : (p:ℕ) ≠ 47)]


lemma thrKey_2 : ∀ j ∈ thrJ 2, Fq (thrV 2 j) 1 ≤ Fq 2 j := by
  intro j hj
  rw [thrJ_eq_2, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_2 : ∀ j ∈ thrJ 2, Fq 2 j < Fq (thrPrev 2 j) 1 := by
  intro j hj
  rw [thrJ_eq_2, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_2 : ∀ j ∈ thrJ 2, 2 ≤ thrV 2 j := by
  intro j hj
  rw [thrJ_eq_2, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_2 : ∀ j ∈ thrJ 2, Nat.Prime (thrPrev 2 j) ∧ thrPrev 2 j < thrV 2 j ∧ (∀ q, Nat.Prime q → q < thrV 2 j → q ≤ thrPrev 2 j) := by
  intro j hj
  rw [thrJ_eq_2, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_2 : Fq 2 13 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_3 : ∀ j ∈ thrJ 3, Fq (thrV 3 j) 1 ≤ Fq 3 j := by
  intro j hj
  rw [thrJ_eq_3, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_3 : ∀ j ∈ thrJ 3, Fq 3 j < Fq (thrPrev 3 j) 1 := by
  intro j hj
  rw [thrJ_eq_3, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_3 : ∀ j ∈ thrJ 3, 2 ≤ thrV 3 j := by
  intro j hj
  rw [thrJ_eq_3, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_3 : ∀ j ∈ thrJ 3, Nat.Prime (thrPrev 3 j) ∧ thrPrev 3 j < thrV 3 j ∧ (∀ q, Nat.Prime q → q < thrV 3 j → q ≤ thrPrev 3 j) := by
  intro j hj
  rw [thrJ_eq_3, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_3 : Fq 3 9 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_5 : ∀ j ∈ thrJ 5, Fq (thrV 5 j) 1 ≤ Fq 5 j := by
  intro j hj
  rw [thrJ_eq_5, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_5 : ∀ j ∈ thrJ 5, Fq 5 j < Fq (thrPrev 5 j) 1 := by
  intro j hj
  rw [thrJ_eq_5, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_5 : ∀ j ∈ thrJ 5, 2 ≤ thrV 5 j := by
  intro j hj
  rw [thrJ_eq_5, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_5 : ∀ j ∈ thrJ 5, Nat.Prime (thrPrev 5 j) ∧ thrPrev 5 j < thrV 5 j ∧ (∀ q, Nat.Prime q → q < thrV 5 j → q ≤ thrPrev 5 j) := by
  intro j hj
  rw [thrJ_eq_5, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_5 : Fq 5 6 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_7 : ∀ j ∈ thrJ 7, Fq (thrV 7 j) 1 ≤ Fq 7 j := by
  intro j hj
  rw [thrJ_eq_7, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_7 : ∀ j ∈ thrJ 7, Fq 7 j < Fq (thrPrev 7 j) 1 := by
  intro j hj
  rw [thrJ_eq_7, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_7 : ∀ j ∈ thrJ 7, 2 ≤ thrV 7 j := by
  intro j hj
  rw [thrJ_eq_7, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_7 : ∀ j ∈ thrJ 7, Nat.Prime (thrPrev 7 j) ∧ thrPrev 7 j < thrV 7 j ∧ (∀ q, Nat.Prime q → q < thrV 7 j → q ≤ thrPrev 7 j) := by
  intro j hj
  rw [thrJ_eq_7, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_7 : Fq 7 5 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_11 : ∀ j ∈ thrJ 11, Fq (thrV 11 j) 1 ≤ Fq 11 j := by
  intro j hj
  rw [thrJ_eq_11, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_11 : ∀ j ∈ thrJ 11, Fq 11 j < Fq (thrPrev 11 j) 1 := by
  intro j hj
  rw [thrJ_eq_11, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_11 : ∀ j ∈ thrJ 11, 2 ≤ thrV 11 j := by
  intro j hj
  rw [thrJ_eq_11, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_11 : ∀ j ∈ thrJ 11, Nat.Prime (thrPrev 11 j) ∧ thrPrev 11 j < thrV 11 j ∧ (∀ q, Nat.Prime q → q < thrV 11 j → q ≤ thrPrev 11 j) := by
  intro j hj
  rw [thrJ_eq_11, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_11 : Fq 11 4 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_13 : ∀ j ∈ thrJ 13, Fq (thrV 13 j) 1 ≤ Fq 13 j := by
  intro j hj
  rw [thrJ_eq_13, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_13 : ∀ j ∈ thrJ 13, Fq 13 j < Fq (thrPrev 13 j) 1 := by
  intro j hj
  rw [thrJ_eq_13, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_13 : ∀ j ∈ thrJ 13, 2 ≤ thrV 13 j := by
  intro j hj
  rw [thrJ_eq_13, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_13 : ∀ j ∈ thrJ 13, Nat.Prime (thrPrev 13 j) ∧ thrPrev 13 j < thrV 13 j ∧ (∀ q, Nat.Prime q → q < thrV 13 j → q ≤ thrPrev 13 j) := by
  intro j hj
  rw [thrJ_eq_13, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_13 : Fq 13 4 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_17 : ∀ j ∈ thrJ 17, Fq (thrV 17 j) 1 ≤ Fq 17 j := by
  intro j hj
  rw [thrJ_eq_17, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_17 : ∀ j ∈ thrJ 17, Fq 17 j < Fq (thrPrev 17 j) 1 := by
  intro j hj
  rw [thrJ_eq_17, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_17 : ∀ j ∈ thrJ 17, 2 ≤ thrV 17 j := by
  intro j hj
  rw [thrJ_eq_17, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_17 : ∀ j ∈ thrJ 17, Nat.Prime (thrPrev 17 j) ∧ thrPrev 17 j < thrV 17 j ∧ (∀ q, Nat.Prime q → q < thrV 17 j → q ≤ thrPrev 17 j) := by
  intro j hj
  rw [thrJ_eq_17, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_17 : Fq 17 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_19 : ∀ j ∈ thrJ 19, Fq (thrV 19 j) 1 ≤ Fq 19 j := by
  intro j hj
  rw [thrJ_eq_19, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_19 : ∀ j ∈ thrJ 19, Fq 19 j < Fq (thrPrev 19 j) 1 := by
  intro j hj
  rw [thrJ_eq_19, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_19 : ∀ j ∈ thrJ 19, 2 ≤ thrV 19 j := by
  intro j hj
  rw [thrJ_eq_19, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_19 : ∀ j ∈ thrJ 19, Nat.Prime (thrPrev 19 j) ∧ thrPrev 19 j < thrV 19 j ∧ (∀ q, Nat.Prime q → q < thrV 19 j → q ≤ thrPrev 19 j) := by
  intro j hj
  rw [thrJ_eq_19, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_19 : Fq 19 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_23 : ∀ j ∈ thrJ 23, Fq (thrV 23 j) 1 ≤ Fq 23 j := by
  intro j hj
  rw [thrJ_eq_23, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_23 : ∀ j ∈ thrJ 23, Fq 23 j < Fq (thrPrev 23 j) 1 := by
  intro j hj
  rw [thrJ_eq_23, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_23 : ∀ j ∈ thrJ 23, 2 ≤ thrV 23 j := by
  intro j hj
  rw [thrJ_eq_23, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_23 : ∀ j ∈ thrJ 23, Nat.Prime (thrPrev 23 j) ∧ thrPrev 23 j < thrV 23 j ∧ (∀ q, Nat.Prime q → q < thrV 23 j → q ≤ thrPrev 23 j) := by
  intro j hj
  rw [thrJ_eq_23, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_23 : Fq 23 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_29 : ∀ j ∈ thrJ 29, Fq (thrV 29 j) 1 ≤ Fq 29 j := by
  intro j hj
  rw [thrJ_eq_29, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_29 : ∀ j ∈ thrJ 29, Fq 29 j < Fq (thrPrev 29 j) 1 := by
  intro j hj
  rw [thrJ_eq_29, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_29 : ∀ j ∈ thrJ 29, 2 ≤ thrV 29 j := by
  intro j hj
  rw [thrJ_eq_29, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_29 : ∀ j ∈ thrJ 29, Nat.Prime (thrPrev 29 j) ∧ thrPrev 29 j < thrV 29 j ∧ (∀ q, Nat.Prime q → q < thrV 29 j → q ≤ thrPrev 29 j) := by
  intro j hj
  rw [thrJ_eq_29, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_29 : Fq 29 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_31 : ∀ j ∈ thrJ 31, Fq (thrV 31 j) 1 ≤ Fq 31 j := by
  intro j hj
  rw [thrJ_eq_31, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_31 : ∀ j ∈ thrJ 31, Fq 31 j < Fq (thrPrev 31 j) 1 := by
  intro j hj
  rw [thrJ_eq_31, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_31 : ∀ j ∈ thrJ 31, 2 ≤ thrV 31 j := by
  intro j hj
  rw [thrJ_eq_31, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_31 : ∀ j ∈ thrJ 31, Nat.Prime (thrPrev 31 j) ∧ thrPrev 31 j < thrV 31 j ∧ (∀ q, Nat.Prime q → q < thrV 31 j → q ≤ thrPrev 31 j) := by
  intro j hj
  rw [thrJ_eq_31, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_31 : Fq 31 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_37 : ∀ j ∈ thrJ 37, Fq (thrV 37 j) 1 ≤ Fq 37 j := by
  intro j hj
  rw [thrJ_eq_37, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_37 : ∀ j ∈ thrJ 37, Fq 37 j < Fq (thrPrev 37 j) 1 := by
  intro j hj
  rw [thrJ_eq_37, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_37 : ∀ j ∈ thrJ 37, 2 ≤ thrV 37 j := by
  intro j hj
  rw [thrJ_eq_37, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_37 : ∀ j ∈ thrJ 37, Nat.Prime (thrPrev 37 j) ∧ thrPrev 37 j < thrV 37 j ∧ (∀ q, Nat.Prime q → q < thrV 37 j → q ≤ thrPrev 37 j) := by
  intro j hj
  rw [thrJ_eq_37, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_37 : Fq 37 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_41 : ∀ j ∈ thrJ 41, Fq (thrV 41 j) 1 ≤ Fq 41 j := by
  intro j hj
  rw [thrJ_eq_41, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_41 : ∀ j ∈ thrJ 41, Fq 41 j < Fq (thrPrev 41 j) 1 := by
  intro j hj
  rw [thrJ_eq_41, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_41 : ∀ j ∈ thrJ 41, 2 ≤ thrV 41 j := by
  intro j hj
  rw [thrJ_eq_41, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_41 : ∀ j ∈ thrJ 41, Nat.Prime (thrPrev 41 j) ∧ thrPrev 41 j < thrV 41 j ∧ (∀ q, Nat.Prime q → q < thrV 41 j → q ≤ thrPrev 41 j) := by
  intro j hj
  rw [thrJ_eq_41, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_41 : Fq 41 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_43 : ∀ j ∈ thrJ 43, Fq (thrV 43 j) 1 ≤ Fq 43 j := by
  intro j hj
  rw [thrJ_eq_43, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_43 : ∀ j ∈ thrJ 43, Fq 43 j < Fq (thrPrev 43 j) 1 := by
  intro j hj
  rw [thrJ_eq_43, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_43 : ∀ j ∈ thrJ 43, 2 ≤ thrV 43 j := by
  intro j hj
  rw [thrJ_eq_43, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_43 : ∀ j ∈ thrJ 43, Nat.Prime (thrPrev 43 j) ∧ thrPrev 43 j < thrV 43 j ∧ (∀ q, Nat.Prime q → q < thrV 43 j → q ≤ thrPrev 43 j) := by
  intro j hj
  rw [thrJ_eq_43, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_43 : Fq 43 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma thrKey_47 : ∀ j ∈ thrJ 47, Fq (thrV 47 j) 1 ≤ Fq 47 j := by
  intro j hj
  rw [thrJ_eq_47, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;>
    (apply F1_le_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrKeyGtAll_47 : ∀ j ∈ thrJ 47, Fq 47 j < Fq (thrPrev 47 j) 1 := by
  intro j hj
  rw [thrJ_eq_47, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrPrev] <;>
    (apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
     decide +kernel)

lemma thrV_ge_two_47 : ∀ j ∈ thrJ 47, 2 ≤ thrV 47 j := by
  intro j hj
  rw [thrJ_eq_47, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j <;> simp only [thrV] <;> norm_num

lemma thrPrev_spec_47 : ∀ j ∈ thrJ 47, Nat.Prime (thrPrev 47 j) ∧ thrPrev 47 j < thrV 47 j ∧ (∀ q, Nat.Prime q → q < thrV 47 j → q ≤ thrPrev 47 j) := by
  intro j hj
  rw [thrJ_eq_47, Finset.mem_Icc] at hj
  obtain ⟨h2,hJ⟩ := hj
  interval_cases j

  · refine ⟨by decide, by decide, ?_⟩
    intro q hq hlt
    simp only [thrV] at hlt
    by_contra hcon
    rw [not_le] at hcon
    simp only [thrPrev] at hcon
    interval_cases q <;> (exfalso; revert hq; decide)


lemma cut_47 : Fq 47 3 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel


lemma F53 : Fq 53 2 < Fq 19 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel

lemma thrJ_val_0 : thrJ 0 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (0:ℕ) ≠ 2)]
  rw [if_neg (by decide : (0:ℕ) ≠ 3)]
  rw [if_neg (by decide : (0:ℕ) ≠ 5)]
  rw [if_neg (by decide : (0:ℕ) ≠ 7)]
  rw [if_neg (by decide : (0:ℕ) ≠ 11)]
  rw [if_neg (by decide : (0:ℕ) ≠ 13)]
  rw [if_neg (by decide : (0:ℕ) ≠ 17)]
  rw [if_neg (by decide : (0:ℕ) ≠ 19)]
  rw [if_neg (by decide : (0:ℕ) ≠ 23)]
  rw [if_neg (by decide : (0:ℕ) ≠ 29)]
  rw [if_neg (by decide : (0:ℕ) ≠ 31)]
  rw [if_neg (by decide : (0:ℕ) ≠ 37)]
  rw [if_neg (by decide : (0:ℕ) ≠ 41)]
  rw [if_neg (by decide : (0:ℕ) ≠ 43)]
  rw [if_neg (by decide : (0:ℕ) ≠ 47)]


lemma thrJ_val_1 : thrJ 1 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (1:ℕ) ≠ 2)]
  rw [if_neg (by decide : (1:ℕ) ≠ 3)]
  rw [if_neg (by decide : (1:ℕ) ≠ 5)]
  rw [if_neg (by decide : (1:ℕ) ≠ 7)]
  rw [if_neg (by decide : (1:ℕ) ≠ 11)]
  rw [if_neg (by decide : (1:ℕ) ≠ 13)]
  rw [if_neg (by decide : (1:ℕ) ≠ 17)]
  rw [if_neg (by decide : (1:ℕ) ≠ 19)]
  rw [if_neg (by decide : (1:ℕ) ≠ 23)]
  rw [if_neg (by decide : (1:ℕ) ≠ 29)]
  rw [if_neg (by decide : (1:ℕ) ≠ 31)]
  rw [if_neg (by decide : (1:ℕ) ≠ 37)]
  rw [if_neg (by decide : (1:ℕ) ≠ 41)]
  rw [if_neg (by decide : (1:ℕ) ≠ 43)]
  rw [if_neg (by decide : (1:ℕ) ≠ 47)]


lemma thrJ_val_2 : thrJ 2 = Finset.Icc 2 12 := thrJ_eq_2


lemma thrJ_val_3 : thrJ 3 = Finset.Icc 2 8 := thrJ_eq_3


lemma thrJ_val_4 : thrJ 4 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (4:ℕ) ≠ 2)]
  rw [if_neg (by decide : (4:ℕ) ≠ 3)]
  rw [if_neg (by decide : (4:ℕ) ≠ 5)]
  rw [if_neg (by decide : (4:ℕ) ≠ 7)]
  rw [if_neg (by decide : (4:ℕ) ≠ 11)]
  rw [if_neg (by decide : (4:ℕ) ≠ 13)]
  rw [if_neg (by decide : (4:ℕ) ≠ 17)]
  rw [if_neg (by decide : (4:ℕ) ≠ 19)]
  rw [if_neg (by decide : (4:ℕ) ≠ 23)]
  rw [if_neg (by decide : (4:ℕ) ≠ 29)]
  rw [if_neg (by decide : (4:ℕ) ≠ 31)]
  rw [if_neg (by decide : (4:ℕ) ≠ 37)]
  rw [if_neg (by decide : (4:ℕ) ≠ 41)]
  rw [if_neg (by decide : (4:ℕ) ≠ 43)]
  rw [if_neg (by decide : (4:ℕ) ≠ 47)]


lemma thrJ_val_5 : thrJ 5 = Finset.Icc 2 5 := thrJ_eq_5


lemma thrJ_val_6 : thrJ 6 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (6:ℕ) ≠ 2)]
  rw [if_neg (by decide : (6:ℕ) ≠ 3)]
  rw [if_neg (by decide : (6:ℕ) ≠ 5)]
  rw [if_neg (by decide : (6:ℕ) ≠ 7)]
  rw [if_neg (by decide : (6:ℕ) ≠ 11)]
  rw [if_neg (by decide : (6:ℕ) ≠ 13)]
  rw [if_neg (by decide : (6:ℕ) ≠ 17)]
  rw [if_neg (by decide : (6:ℕ) ≠ 19)]
  rw [if_neg (by decide : (6:ℕ) ≠ 23)]
  rw [if_neg (by decide : (6:ℕ) ≠ 29)]
  rw [if_neg (by decide : (6:ℕ) ≠ 31)]
  rw [if_neg (by decide : (6:ℕ) ≠ 37)]
  rw [if_neg (by decide : (6:ℕ) ≠ 41)]
  rw [if_neg (by decide : (6:ℕ) ≠ 43)]
  rw [if_neg (by decide : (6:ℕ) ≠ 47)]


lemma thrJ_val_7 : thrJ 7 = Finset.Icc 2 4 := thrJ_eq_7


lemma thrJ_val_8 : thrJ 8 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (8:ℕ) ≠ 2)]
  rw [if_neg (by decide : (8:ℕ) ≠ 3)]
  rw [if_neg (by decide : (8:ℕ) ≠ 5)]
  rw [if_neg (by decide : (8:ℕ) ≠ 7)]
  rw [if_neg (by decide : (8:ℕ) ≠ 11)]
  rw [if_neg (by decide : (8:ℕ) ≠ 13)]
  rw [if_neg (by decide : (8:ℕ) ≠ 17)]
  rw [if_neg (by decide : (8:ℕ) ≠ 19)]
  rw [if_neg (by decide : (8:ℕ) ≠ 23)]
  rw [if_neg (by decide : (8:ℕ) ≠ 29)]
  rw [if_neg (by decide : (8:ℕ) ≠ 31)]
  rw [if_neg (by decide : (8:ℕ) ≠ 37)]
  rw [if_neg (by decide : (8:ℕ) ≠ 41)]
  rw [if_neg (by decide : (8:ℕ) ≠ 43)]
  rw [if_neg (by decide : (8:ℕ) ≠ 47)]


lemma thrJ_val_9 : thrJ 9 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (9:ℕ) ≠ 2)]
  rw [if_neg (by decide : (9:ℕ) ≠ 3)]
  rw [if_neg (by decide : (9:ℕ) ≠ 5)]
  rw [if_neg (by decide : (9:ℕ) ≠ 7)]
  rw [if_neg (by decide : (9:ℕ) ≠ 11)]
  rw [if_neg (by decide : (9:ℕ) ≠ 13)]
  rw [if_neg (by decide : (9:ℕ) ≠ 17)]
  rw [if_neg (by decide : (9:ℕ) ≠ 19)]
  rw [if_neg (by decide : (9:ℕ) ≠ 23)]
  rw [if_neg (by decide : (9:ℕ) ≠ 29)]
  rw [if_neg (by decide : (9:ℕ) ≠ 31)]
  rw [if_neg (by decide : (9:ℕ) ≠ 37)]
  rw [if_neg (by decide : (9:ℕ) ≠ 41)]
  rw [if_neg (by decide : (9:ℕ) ≠ 43)]
  rw [if_neg (by decide : (9:ℕ) ≠ 47)]


lemma thrJ_val_10 : thrJ 10 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (10:ℕ) ≠ 2)]
  rw [if_neg (by decide : (10:ℕ) ≠ 3)]
  rw [if_neg (by decide : (10:ℕ) ≠ 5)]
  rw [if_neg (by decide : (10:ℕ) ≠ 7)]
  rw [if_neg (by decide : (10:ℕ) ≠ 11)]
  rw [if_neg (by decide : (10:ℕ) ≠ 13)]
  rw [if_neg (by decide : (10:ℕ) ≠ 17)]
  rw [if_neg (by decide : (10:ℕ) ≠ 19)]
  rw [if_neg (by decide : (10:ℕ) ≠ 23)]
  rw [if_neg (by decide : (10:ℕ) ≠ 29)]
  rw [if_neg (by decide : (10:ℕ) ≠ 31)]
  rw [if_neg (by decide : (10:ℕ) ≠ 37)]
  rw [if_neg (by decide : (10:ℕ) ≠ 41)]
  rw [if_neg (by decide : (10:ℕ) ≠ 43)]
  rw [if_neg (by decide : (10:ℕ) ≠ 47)]


lemma thrJ_val_11 : thrJ 11 = Finset.Icc 2 3 := thrJ_eq_11


lemma thrJ_val_12 : thrJ 12 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (12:ℕ) ≠ 2)]
  rw [if_neg (by decide : (12:ℕ) ≠ 3)]
  rw [if_neg (by decide : (12:ℕ) ≠ 5)]
  rw [if_neg (by decide : (12:ℕ) ≠ 7)]
  rw [if_neg (by decide : (12:ℕ) ≠ 11)]
  rw [if_neg (by decide : (12:ℕ) ≠ 13)]
  rw [if_neg (by decide : (12:ℕ) ≠ 17)]
  rw [if_neg (by decide : (12:ℕ) ≠ 19)]
  rw [if_neg (by decide : (12:ℕ) ≠ 23)]
  rw [if_neg (by decide : (12:ℕ) ≠ 29)]
  rw [if_neg (by decide : (12:ℕ) ≠ 31)]
  rw [if_neg (by decide : (12:ℕ) ≠ 37)]
  rw [if_neg (by decide : (12:ℕ) ≠ 41)]
  rw [if_neg (by decide : (12:ℕ) ≠ 43)]
  rw [if_neg (by decide : (12:ℕ) ≠ 47)]


lemma thrJ_val_13 : thrJ 13 = Finset.Icc 2 3 := thrJ_eq_13


lemma thrJ_val_14 : thrJ 14 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (14:ℕ) ≠ 2)]
  rw [if_neg (by decide : (14:ℕ) ≠ 3)]
  rw [if_neg (by decide : (14:ℕ) ≠ 5)]
  rw [if_neg (by decide : (14:ℕ) ≠ 7)]
  rw [if_neg (by decide : (14:ℕ) ≠ 11)]
  rw [if_neg (by decide : (14:ℕ) ≠ 13)]
  rw [if_neg (by decide : (14:ℕ) ≠ 17)]
  rw [if_neg (by decide : (14:ℕ) ≠ 19)]
  rw [if_neg (by decide : (14:ℕ) ≠ 23)]
  rw [if_neg (by decide : (14:ℕ) ≠ 29)]
  rw [if_neg (by decide : (14:ℕ) ≠ 31)]
  rw [if_neg (by decide : (14:ℕ) ≠ 37)]
  rw [if_neg (by decide : (14:ℕ) ≠ 41)]
  rw [if_neg (by decide : (14:ℕ) ≠ 43)]
  rw [if_neg (by decide : (14:ℕ) ≠ 47)]


lemma thrJ_val_15 : thrJ 15 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (15:ℕ) ≠ 2)]
  rw [if_neg (by decide : (15:ℕ) ≠ 3)]
  rw [if_neg (by decide : (15:ℕ) ≠ 5)]
  rw [if_neg (by decide : (15:ℕ) ≠ 7)]
  rw [if_neg (by decide : (15:ℕ) ≠ 11)]
  rw [if_neg (by decide : (15:ℕ) ≠ 13)]
  rw [if_neg (by decide : (15:ℕ) ≠ 17)]
  rw [if_neg (by decide : (15:ℕ) ≠ 19)]
  rw [if_neg (by decide : (15:ℕ) ≠ 23)]
  rw [if_neg (by decide : (15:ℕ) ≠ 29)]
  rw [if_neg (by decide : (15:ℕ) ≠ 31)]
  rw [if_neg (by decide : (15:ℕ) ≠ 37)]
  rw [if_neg (by decide : (15:ℕ) ≠ 41)]
  rw [if_neg (by decide : (15:ℕ) ≠ 43)]
  rw [if_neg (by decide : (15:ℕ) ≠ 47)]


lemma thrJ_val_16 : thrJ 16 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (16:ℕ) ≠ 2)]
  rw [if_neg (by decide : (16:ℕ) ≠ 3)]
  rw [if_neg (by decide : (16:ℕ) ≠ 5)]
  rw [if_neg (by decide : (16:ℕ) ≠ 7)]
  rw [if_neg (by decide : (16:ℕ) ≠ 11)]
  rw [if_neg (by decide : (16:ℕ) ≠ 13)]
  rw [if_neg (by decide : (16:ℕ) ≠ 17)]
  rw [if_neg (by decide : (16:ℕ) ≠ 19)]
  rw [if_neg (by decide : (16:ℕ) ≠ 23)]
  rw [if_neg (by decide : (16:ℕ) ≠ 29)]
  rw [if_neg (by decide : (16:ℕ) ≠ 31)]
  rw [if_neg (by decide : (16:ℕ) ≠ 37)]
  rw [if_neg (by decide : (16:ℕ) ≠ 41)]
  rw [if_neg (by decide : (16:ℕ) ≠ 43)]
  rw [if_neg (by decide : (16:ℕ) ≠ 47)]


lemma thrJ_val_17 : thrJ 17 = Finset.Icc 2 2 := thrJ_eq_17


lemma thrJ_val_18 : thrJ 18 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (18:ℕ) ≠ 2)]
  rw [if_neg (by decide : (18:ℕ) ≠ 3)]
  rw [if_neg (by decide : (18:ℕ) ≠ 5)]
  rw [if_neg (by decide : (18:ℕ) ≠ 7)]
  rw [if_neg (by decide : (18:ℕ) ≠ 11)]
  rw [if_neg (by decide : (18:ℕ) ≠ 13)]
  rw [if_neg (by decide : (18:ℕ) ≠ 17)]
  rw [if_neg (by decide : (18:ℕ) ≠ 19)]
  rw [if_neg (by decide : (18:ℕ) ≠ 23)]
  rw [if_neg (by decide : (18:ℕ) ≠ 29)]
  rw [if_neg (by decide : (18:ℕ) ≠ 31)]
  rw [if_neg (by decide : (18:ℕ) ≠ 37)]
  rw [if_neg (by decide : (18:ℕ) ≠ 41)]
  rw [if_neg (by decide : (18:ℕ) ≠ 43)]
  rw [if_neg (by decide : (18:ℕ) ≠ 47)]


lemma thrJ_val_19 : thrJ 19 = Finset.Icc 2 2 := thrJ_eq_19


lemma thrJ_val_20 : thrJ 20 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (20:ℕ) ≠ 2)]
  rw [if_neg (by decide : (20:ℕ) ≠ 3)]
  rw [if_neg (by decide : (20:ℕ) ≠ 5)]
  rw [if_neg (by decide : (20:ℕ) ≠ 7)]
  rw [if_neg (by decide : (20:ℕ) ≠ 11)]
  rw [if_neg (by decide : (20:ℕ) ≠ 13)]
  rw [if_neg (by decide : (20:ℕ) ≠ 17)]
  rw [if_neg (by decide : (20:ℕ) ≠ 19)]
  rw [if_neg (by decide : (20:ℕ) ≠ 23)]
  rw [if_neg (by decide : (20:ℕ) ≠ 29)]
  rw [if_neg (by decide : (20:ℕ) ≠ 31)]
  rw [if_neg (by decide : (20:ℕ) ≠ 37)]
  rw [if_neg (by decide : (20:ℕ) ≠ 41)]
  rw [if_neg (by decide : (20:ℕ) ≠ 43)]
  rw [if_neg (by decide : (20:ℕ) ≠ 47)]


lemma thrJ_val_21 : thrJ 21 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (21:ℕ) ≠ 2)]
  rw [if_neg (by decide : (21:ℕ) ≠ 3)]
  rw [if_neg (by decide : (21:ℕ) ≠ 5)]
  rw [if_neg (by decide : (21:ℕ) ≠ 7)]
  rw [if_neg (by decide : (21:ℕ) ≠ 11)]
  rw [if_neg (by decide : (21:ℕ) ≠ 13)]
  rw [if_neg (by decide : (21:ℕ) ≠ 17)]
  rw [if_neg (by decide : (21:ℕ) ≠ 19)]
  rw [if_neg (by decide : (21:ℕ) ≠ 23)]
  rw [if_neg (by decide : (21:ℕ) ≠ 29)]
  rw [if_neg (by decide : (21:ℕ) ≠ 31)]
  rw [if_neg (by decide : (21:ℕ) ≠ 37)]
  rw [if_neg (by decide : (21:ℕ) ≠ 41)]
  rw [if_neg (by decide : (21:ℕ) ≠ 43)]
  rw [if_neg (by decide : (21:ℕ) ≠ 47)]


lemma thrJ_val_22 : thrJ 22 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (22:ℕ) ≠ 2)]
  rw [if_neg (by decide : (22:ℕ) ≠ 3)]
  rw [if_neg (by decide : (22:ℕ) ≠ 5)]
  rw [if_neg (by decide : (22:ℕ) ≠ 7)]
  rw [if_neg (by decide : (22:ℕ) ≠ 11)]
  rw [if_neg (by decide : (22:ℕ) ≠ 13)]
  rw [if_neg (by decide : (22:ℕ) ≠ 17)]
  rw [if_neg (by decide : (22:ℕ) ≠ 19)]
  rw [if_neg (by decide : (22:ℕ) ≠ 23)]
  rw [if_neg (by decide : (22:ℕ) ≠ 29)]
  rw [if_neg (by decide : (22:ℕ) ≠ 31)]
  rw [if_neg (by decide : (22:ℕ) ≠ 37)]
  rw [if_neg (by decide : (22:ℕ) ≠ 41)]
  rw [if_neg (by decide : (22:ℕ) ≠ 43)]
  rw [if_neg (by decide : (22:ℕ) ≠ 47)]


lemma thrJ_val_23 : thrJ 23 = Finset.Icc 2 2 := thrJ_eq_23


lemma thrJ_val_24 : thrJ 24 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (24:ℕ) ≠ 2)]
  rw [if_neg (by decide : (24:ℕ) ≠ 3)]
  rw [if_neg (by decide : (24:ℕ) ≠ 5)]
  rw [if_neg (by decide : (24:ℕ) ≠ 7)]
  rw [if_neg (by decide : (24:ℕ) ≠ 11)]
  rw [if_neg (by decide : (24:ℕ) ≠ 13)]
  rw [if_neg (by decide : (24:ℕ) ≠ 17)]
  rw [if_neg (by decide : (24:ℕ) ≠ 19)]
  rw [if_neg (by decide : (24:ℕ) ≠ 23)]
  rw [if_neg (by decide : (24:ℕ) ≠ 29)]
  rw [if_neg (by decide : (24:ℕ) ≠ 31)]
  rw [if_neg (by decide : (24:ℕ) ≠ 37)]
  rw [if_neg (by decide : (24:ℕ) ≠ 41)]
  rw [if_neg (by decide : (24:ℕ) ≠ 43)]
  rw [if_neg (by decide : (24:ℕ) ≠ 47)]


lemma thrJ_val_25 : thrJ 25 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (25:ℕ) ≠ 2)]
  rw [if_neg (by decide : (25:ℕ) ≠ 3)]
  rw [if_neg (by decide : (25:ℕ) ≠ 5)]
  rw [if_neg (by decide : (25:ℕ) ≠ 7)]
  rw [if_neg (by decide : (25:ℕ) ≠ 11)]
  rw [if_neg (by decide : (25:ℕ) ≠ 13)]
  rw [if_neg (by decide : (25:ℕ) ≠ 17)]
  rw [if_neg (by decide : (25:ℕ) ≠ 19)]
  rw [if_neg (by decide : (25:ℕ) ≠ 23)]
  rw [if_neg (by decide : (25:ℕ) ≠ 29)]
  rw [if_neg (by decide : (25:ℕ) ≠ 31)]
  rw [if_neg (by decide : (25:ℕ) ≠ 37)]
  rw [if_neg (by decide : (25:ℕ) ≠ 41)]
  rw [if_neg (by decide : (25:ℕ) ≠ 43)]
  rw [if_neg (by decide : (25:ℕ) ≠ 47)]


lemma thrJ_val_26 : thrJ 26 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (26:ℕ) ≠ 2)]
  rw [if_neg (by decide : (26:ℕ) ≠ 3)]
  rw [if_neg (by decide : (26:ℕ) ≠ 5)]
  rw [if_neg (by decide : (26:ℕ) ≠ 7)]
  rw [if_neg (by decide : (26:ℕ) ≠ 11)]
  rw [if_neg (by decide : (26:ℕ) ≠ 13)]
  rw [if_neg (by decide : (26:ℕ) ≠ 17)]
  rw [if_neg (by decide : (26:ℕ) ≠ 19)]
  rw [if_neg (by decide : (26:ℕ) ≠ 23)]
  rw [if_neg (by decide : (26:ℕ) ≠ 29)]
  rw [if_neg (by decide : (26:ℕ) ≠ 31)]
  rw [if_neg (by decide : (26:ℕ) ≠ 37)]
  rw [if_neg (by decide : (26:ℕ) ≠ 41)]
  rw [if_neg (by decide : (26:ℕ) ≠ 43)]
  rw [if_neg (by decide : (26:ℕ) ≠ 47)]


lemma thrJ_val_27 : thrJ 27 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (27:ℕ) ≠ 2)]
  rw [if_neg (by decide : (27:ℕ) ≠ 3)]
  rw [if_neg (by decide : (27:ℕ) ≠ 5)]
  rw [if_neg (by decide : (27:ℕ) ≠ 7)]
  rw [if_neg (by decide : (27:ℕ) ≠ 11)]
  rw [if_neg (by decide : (27:ℕ) ≠ 13)]
  rw [if_neg (by decide : (27:ℕ) ≠ 17)]
  rw [if_neg (by decide : (27:ℕ) ≠ 19)]
  rw [if_neg (by decide : (27:ℕ) ≠ 23)]
  rw [if_neg (by decide : (27:ℕ) ≠ 29)]
  rw [if_neg (by decide : (27:ℕ) ≠ 31)]
  rw [if_neg (by decide : (27:ℕ) ≠ 37)]
  rw [if_neg (by decide : (27:ℕ) ≠ 41)]
  rw [if_neg (by decide : (27:ℕ) ≠ 43)]
  rw [if_neg (by decide : (27:ℕ) ≠ 47)]


lemma thrJ_val_28 : thrJ 28 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (28:ℕ) ≠ 2)]
  rw [if_neg (by decide : (28:ℕ) ≠ 3)]
  rw [if_neg (by decide : (28:ℕ) ≠ 5)]
  rw [if_neg (by decide : (28:ℕ) ≠ 7)]
  rw [if_neg (by decide : (28:ℕ) ≠ 11)]
  rw [if_neg (by decide : (28:ℕ) ≠ 13)]
  rw [if_neg (by decide : (28:ℕ) ≠ 17)]
  rw [if_neg (by decide : (28:ℕ) ≠ 19)]
  rw [if_neg (by decide : (28:ℕ) ≠ 23)]
  rw [if_neg (by decide : (28:ℕ) ≠ 29)]
  rw [if_neg (by decide : (28:ℕ) ≠ 31)]
  rw [if_neg (by decide : (28:ℕ) ≠ 37)]
  rw [if_neg (by decide : (28:ℕ) ≠ 41)]
  rw [if_neg (by decide : (28:ℕ) ≠ 43)]
  rw [if_neg (by decide : (28:ℕ) ≠ 47)]


lemma thrJ_val_29 : thrJ 29 = Finset.Icc 2 2 := thrJ_eq_29


lemma thrJ_val_30 : thrJ 30 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (30:ℕ) ≠ 2)]
  rw [if_neg (by decide : (30:ℕ) ≠ 3)]
  rw [if_neg (by decide : (30:ℕ) ≠ 5)]
  rw [if_neg (by decide : (30:ℕ) ≠ 7)]
  rw [if_neg (by decide : (30:ℕ) ≠ 11)]
  rw [if_neg (by decide : (30:ℕ) ≠ 13)]
  rw [if_neg (by decide : (30:ℕ) ≠ 17)]
  rw [if_neg (by decide : (30:ℕ) ≠ 19)]
  rw [if_neg (by decide : (30:ℕ) ≠ 23)]
  rw [if_neg (by decide : (30:ℕ) ≠ 29)]
  rw [if_neg (by decide : (30:ℕ) ≠ 31)]
  rw [if_neg (by decide : (30:ℕ) ≠ 37)]
  rw [if_neg (by decide : (30:ℕ) ≠ 41)]
  rw [if_neg (by decide : (30:ℕ) ≠ 43)]
  rw [if_neg (by decide : (30:ℕ) ≠ 47)]


lemma thrJ_val_31 : thrJ 31 = Finset.Icc 2 2 := thrJ_eq_31


lemma thrJ_val_32 : thrJ 32 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (32:ℕ) ≠ 2)]
  rw [if_neg (by decide : (32:ℕ) ≠ 3)]
  rw [if_neg (by decide : (32:ℕ) ≠ 5)]
  rw [if_neg (by decide : (32:ℕ) ≠ 7)]
  rw [if_neg (by decide : (32:ℕ) ≠ 11)]
  rw [if_neg (by decide : (32:ℕ) ≠ 13)]
  rw [if_neg (by decide : (32:ℕ) ≠ 17)]
  rw [if_neg (by decide : (32:ℕ) ≠ 19)]
  rw [if_neg (by decide : (32:ℕ) ≠ 23)]
  rw [if_neg (by decide : (32:ℕ) ≠ 29)]
  rw [if_neg (by decide : (32:ℕ) ≠ 31)]
  rw [if_neg (by decide : (32:ℕ) ≠ 37)]
  rw [if_neg (by decide : (32:ℕ) ≠ 41)]
  rw [if_neg (by decide : (32:ℕ) ≠ 43)]
  rw [if_neg (by decide : (32:ℕ) ≠ 47)]


lemma thrJ_val_33 : thrJ 33 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (33:ℕ) ≠ 2)]
  rw [if_neg (by decide : (33:ℕ) ≠ 3)]
  rw [if_neg (by decide : (33:ℕ) ≠ 5)]
  rw [if_neg (by decide : (33:ℕ) ≠ 7)]
  rw [if_neg (by decide : (33:ℕ) ≠ 11)]
  rw [if_neg (by decide : (33:ℕ) ≠ 13)]
  rw [if_neg (by decide : (33:ℕ) ≠ 17)]
  rw [if_neg (by decide : (33:ℕ) ≠ 19)]
  rw [if_neg (by decide : (33:ℕ) ≠ 23)]
  rw [if_neg (by decide : (33:ℕ) ≠ 29)]
  rw [if_neg (by decide : (33:ℕ) ≠ 31)]
  rw [if_neg (by decide : (33:ℕ) ≠ 37)]
  rw [if_neg (by decide : (33:ℕ) ≠ 41)]
  rw [if_neg (by decide : (33:ℕ) ≠ 43)]
  rw [if_neg (by decide : (33:ℕ) ≠ 47)]


lemma thrJ_val_34 : thrJ 34 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (34:ℕ) ≠ 2)]
  rw [if_neg (by decide : (34:ℕ) ≠ 3)]
  rw [if_neg (by decide : (34:ℕ) ≠ 5)]
  rw [if_neg (by decide : (34:ℕ) ≠ 7)]
  rw [if_neg (by decide : (34:ℕ) ≠ 11)]
  rw [if_neg (by decide : (34:ℕ) ≠ 13)]
  rw [if_neg (by decide : (34:ℕ) ≠ 17)]
  rw [if_neg (by decide : (34:ℕ) ≠ 19)]
  rw [if_neg (by decide : (34:ℕ) ≠ 23)]
  rw [if_neg (by decide : (34:ℕ) ≠ 29)]
  rw [if_neg (by decide : (34:ℕ) ≠ 31)]
  rw [if_neg (by decide : (34:ℕ) ≠ 37)]
  rw [if_neg (by decide : (34:ℕ) ≠ 41)]
  rw [if_neg (by decide : (34:ℕ) ≠ 43)]
  rw [if_neg (by decide : (34:ℕ) ≠ 47)]


lemma thrJ_val_35 : thrJ 35 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (35:ℕ) ≠ 2)]
  rw [if_neg (by decide : (35:ℕ) ≠ 3)]
  rw [if_neg (by decide : (35:ℕ) ≠ 5)]
  rw [if_neg (by decide : (35:ℕ) ≠ 7)]
  rw [if_neg (by decide : (35:ℕ) ≠ 11)]
  rw [if_neg (by decide : (35:ℕ) ≠ 13)]
  rw [if_neg (by decide : (35:ℕ) ≠ 17)]
  rw [if_neg (by decide : (35:ℕ) ≠ 19)]
  rw [if_neg (by decide : (35:ℕ) ≠ 23)]
  rw [if_neg (by decide : (35:ℕ) ≠ 29)]
  rw [if_neg (by decide : (35:ℕ) ≠ 31)]
  rw [if_neg (by decide : (35:ℕ) ≠ 37)]
  rw [if_neg (by decide : (35:ℕ) ≠ 41)]
  rw [if_neg (by decide : (35:ℕ) ≠ 43)]
  rw [if_neg (by decide : (35:ℕ) ≠ 47)]


lemma thrJ_val_36 : thrJ 36 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (36:ℕ) ≠ 2)]
  rw [if_neg (by decide : (36:ℕ) ≠ 3)]
  rw [if_neg (by decide : (36:ℕ) ≠ 5)]
  rw [if_neg (by decide : (36:ℕ) ≠ 7)]
  rw [if_neg (by decide : (36:ℕ) ≠ 11)]
  rw [if_neg (by decide : (36:ℕ) ≠ 13)]
  rw [if_neg (by decide : (36:ℕ) ≠ 17)]
  rw [if_neg (by decide : (36:ℕ) ≠ 19)]
  rw [if_neg (by decide : (36:ℕ) ≠ 23)]
  rw [if_neg (by decide : (36:ℕ) ≠ 29)]
  rw [if_neg (by decide : (36:ℕ) ≠ 31)]
  rw [if_neg (by decide : (36:ℕ) ≠ 37)]
  rw [if_neg (by decide : (36:ℕ) ≠ 41)]
  rw [if_neg (by decide : (36:ℕ) ≠ 43)]
  rw [if_neg (by decide : (36:ℕ) ≠ 47)]


lemma thrJ_val_37 : thrJ 37 = Finset.Icc 2 2 := thrJ_eq_37


lemma thrJ_val_38 : thrJ 38 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (38:ℕ) ≠ 2)]
  rw [if_neg (by decide : (38:ℕ) ≠ 3)]
  rw [if_neg (by decide : (38:ℕ) ≠ 5)]
  rw [if_neg (by decide : (38:ℕ) ≠ 7)]
  rw [if_neg (by decide : (38:ℕ) ≠ 11)]
  rw [if_neg (by decide : (38:ℕ) ≠ 13)]
  rw [if_neg (by decide : (38:ℕ) ≠ 17)]
  rw [if_neg (by decide : (38:ℕ) ≠ 19)]
  rw [if_neg (by decide : (38:ℕ) ≠ 23)]
  rw [if_neg (by decide : (38:ℕ) ≠ 29)]
  rw [if_neg (by decide : (38:ℕ) ≠ 31)]
  rw [if_neg (by decide : (38:ℕ) ≠ 37)]
  rw [if_neg (by decide : (38:ℕ) ≠ 41)]
  rw [if_neg (by decide : (38:ℕ) ≠ 43)]
  rw [if_neg (by decide : (38:ℕ) ≠ 47)]


lemma thrJ_val_39 : thrJ 39 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (39:ℕ) ≠ 2)]
  rw [if_neg (by decide : (39:ℕ) ≠ 3)]
  rw [if_neg (by decide : (39:ℕ) ≠ 5)]
  rw [if_neg (by decide : (39:ℕ) ≠ 7)]
  rw [if_neg (by decide : (39:ℕ) ≠ 11)]
  rw [if_neg (by decide : (39:ℕ) ≠ 13)]
  rw [if_neg (by decide : (39:ℕ) ≠ 17)]
  rw [if_neg (by decide : (39:ℕ) ≠ 19)]
  rw [if_neg (by decide : (39:ℕ) ≠ 23)]
  rw [if_neg (by decide : (39:ℕ) ≠ 29)]
  rw [if_neg (by decide : (39:ℕ) ≠ 31)]
  rw [if_neg (by decide : (39:ℕ) ≠ 37)]
  rw [if_neg (by decide : (39:ℕ) ≠ 41)]
  rw [if_neg (by decide : (39:ℕ) ≠ 43)]
  rw [if_neg (by decide : (39:ℕ) ≠ 47)]


lemma thrJ_val_40 : thrJ 40 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (40:ℕ) ≠ 2)]
  rw [if_neg (by decide : (40:ℕ) ≠ 3)]
  rw [if_neg (by decide : (40:ℕ) ≠ 5)]
  rw [if_neg (by decide : (40:ℕ) ≠ 7)]
  rw [if_neg (by decide : (40:ℕ) ≠ 11)]
  rw [if_neg (by decide : (40:ℕ) ≠ 13)]
  rw [if_neg (by decide : (40:ℕ) ≠ 17)]
  rw [if_neg (by decide : (40:ℕ) ≠ 19)]
  rw [if_neg (by decide : (40:ℕ) ≠ 23)]
  rw [if_neg (by decide : (40:ℕ) ≠ 29)]
  rw [if_neg (by decide : (40:ℕ) ≠ 31)]
  rw [if_neg (by decide : (40:ℕ) ≠ 37)]
  rw [if_neg (by decide : (40:ℕ) ≠ 41)]
  rw [if_neg (by decide : (40:ℕ) ≠ 43)]
  rw [if_neg (by decide : (40:ℕ) ≠ 47)]


lemma thrJ_val_41 : thrJ 41 = Finset.Icc 2 2 := thrJ_eq_41


lemma thrJ_val_42 : thrJ 42 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (42:ℕ) ≠ 2)]
  rw [if_neg (by decide : (42:ℕ) ≠ 3)]
  rw [if_neg (by decide : (42:ℕ) ≠ 5)]
  rw [if_neg (by decide : (42:ℕ) ≠ 7)]
  rw [if_neg (by decide : (42:ℕ) ≠ 11)]
  rw [if_neg (by decide : (42:ℕ) ≠ 13)]
  rw [if_neg (by decide : (42:ℕ) ≠ 17)]
  rw [if_neg (by decide : (42:ℕ) ≠ 19)]
  rw [if_neg (by decide : (42:ℕ) ≠ 23)]
  rw [if_neg (by decide : (42:ℕ) ≠ 29)]
  rw [if_neg (by decide : (42:ℕ) ≠ 31)]
  rw [if_neg (by decide : (42:ℕ) ≠ 37)]
  rw [if_neg (by decide : (42:ℕ) ≠ 41)]
  rw [if_neg (by decide : (42:ℕ) ≠ 43)]
  rw [if_neg (by decide : (42:ℕ) ≠ 47)]


lemma thrJ_val_43 : thrJ 43 = Finset.Icc 2 2 := thrJ_eq_43


lemma thrJ_val_44 : thrJ 44 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (44:ℕ) ≠ 2)]
  rw [if_neg (by decide : (44:ℕ) ≠ 3)]
  rw [if_neg (by decide : (44:ℕ) ≠ 5)]
  rw [if_neg (by decide : (44:ℕ) ≠ 7)]
  rw [if_neg (by decide : (44:ℕ) ≠ 11)]
  rw [if_neg (by decide : (44:ℕ) ≠ 13)]
  rw [if_neg (by decide : (44:ℕ) ≠ 17)]
  rw [if_neg (by decide : (44:ℕ) ≠ 19)]
  rw [if_neg (by decide : (44:ℕ) ≠ 23)]
  rw [if_neg (by decide : (44:ℕ) ≠ 29)]
  rw [if_neg (by decide : (44:ℕ) ≠ 31)]
  rw [if_neg (by decide : (44:ℕ) ≠ 37)]
  rw [if_neg (by decide : (44:ℕ) ≠ 41)]
  rw [if_neg (by decide : (44:ℕ) ≠ 43)]
  rw [if_neg (by decide : (44:ℕ) ≠ 47)]


lemma thrJ_val_45 : thrJ 45 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (45:ℕ) ≠ 2)]
  rw [if_neg (by decide : (45:ℕ) ≠ 3)]
  rw [if_neg (by decide : (45:ℕ) ≠ 5)]
  rw [if_neg (by decide : (45:ℕ) ≠ 7)]
  rw [if_neg (by decide : (45:ℕ) ≠ 11)]
  rw [if_neg (by decide : (45:ℕ) ≠ 13)]
  rw [if_neg (by decide : (45:ℕ) ≠ 17)]
  rw [if_neg (by decide : (45:ℕ) ≠ 19)]
  rw [if_neg (by decide : (45:ℕ) ≠ 23)]
  rw [if_neg (by decide : (45:ℕ) ≠ 29)]
  rw [if_neg (by decide : (45:ℕ) ≠ 31)]
  rw [if_neg (by decide : (45:ℕ) ≠ 37)]
  rw [if_neg (by decide : (45:ℕ) ≠ 41)]
  rw [if_neg (by decide : (45:ℕ) ≠ 43)]
  rw [if_neg (by decide : (45:ℕ) ≠ 47)]


lemma thrJ_val_46 : thrJ 46 = ∅ := by
  dsimp only [thrJ]
  rw [if_neg (by decide : (46:ℕ) ≠ 2)]
  rw [if_neg (by decide : (46:ℕ) ≠ 3)]
  rw [if_neg (by decide : (46:ℕ) ≠ 5)]
  rw [if_neg (by decide : (46:ℕ) ≠ 7)]
  rw [if_neg (by decide : (46:ℕ) ≠ 11)]
  rw [if_neg (by decide : (46:ℕ) ≠ 13)]
  rw [if_neg (by decide : (46:ℕ) ≠ 17)]
  rw [if_neg (by decide : (46:ℕ) ≠ 19)]
  rw [if_neg (by decide : (46:ℕ) ≠ 23)]
  rw [if_neg (by decide : (46:ℕ) ≠ 29)]
  rw [if_neg (by decide : (46:ℕ) ≠ 31)]
  rw [if_neg (by decide : (46:ℕ) ≠ 37)]
  rw [if_neg (by decide : (46:ℕ) ≠ 41)]
  rw [if_neg (by decide : (46:ℕ) ≠ 43)]
  rw [if_neg (by decide : (46:ℕ) ≠ 47)]


lemma thrJ_val_47 : thrJ 47 = Finset.Icc 2 2 := thrJ_eq_47


lemma thrJ_mem_ge_two {p x : ℕ} (hx : x ∈ thrJ p) : 2 ≤ x := by
  by_cases hp : p ≤ 47
  · interval_cases p

    · rw [thrJ_val_0] at hx; simp at hx

    · rw [thrJ_val_1] at hx; simp at hx

    · rw [thrJ_val_2, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_3, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_4] at hx; simp at hx

    · rw [thrJ_val_5, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_6] at hx; simp at hx

    · rw [thrJ_val_7, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_8] at hx; simp at hx

    · rw [thrJ_val_9] at hx; simp at hx

    · rw [thrJ_val_10] at hx; simp at hx

    · rw [thrJ_val_11, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_12] at hx; simp at hx

    · rw [thrJ_val_13, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_14] at hx; simp at hx

    · rw [thrJ_val_15] at hx; simp at hx

    · rw [thrJ_val_16] at hx; simp at hx

    · rw [thrJ_val_17, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_18] at hx; simp at hx

    · rw [thrJ_val_19, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_20] at hx; simp at hx

    · rw [thrJ_val_21] at hx; simp at hx

    · rw [thrJ_val_22] at hx; simp at hx

    · rw [thrJ_val_23, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_24] at hx; simp at hx

    · rw [thrJ_val_25] at hx; simp at hx

    · rw [thrJ_val_26] at hx; simp at hx

    · rw [thrJ_val_27] at hx; simp at hx

    · rw [thrJ_val_28] at hx; simp at hx

    · rw [thrJ_val_29, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_30] at hx; simp at hx

    · rw [thrJ_val_31, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_32] at hx; simp at hx

    · rw [thrJ_val_33] at hx; simp at hx

    · rw [thrJ_val_34] at hx; simp at hx

    · rw [thrJ_val_35] at hx; simp at hx

    · rw [thrJ_val_36] at hx; simp at hx

    · rw [thrJ_val_37, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_38] at hx; simp at hx

    · rw [thrJ_val_39] at hx; simp at hx

    · rw [thrJ_val_40] at hx; simp at hx

    · rw [thrJ_val_41, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_42] at hx; simp at hx

    · rw [thrJ_val_43, Finset.mem_Icc] at hx; omega

    · rw [thrJ_val_44] at hx; simp at hx

    · rw [thrJ_val_45] at hx; simp at hx

    · rw [thrJ_val_46] at hx; simp at hx

    · rw [thrJ_val_47, Finset.mem_Icc] at hx; omega

  · have hz : thrJ p = ∅ := thrJ_eq_empty_of_ge p (by omega)
    rw [hz] at hx; simp at hx

lemma one_le_kminC (ξ p : ℕ) : 1 ≤ kminC ξ p := by
  have key : ∀ h : (thrSet ξ p).Nonempty, 2 ≤ (thrSet ξ p).max' h := by
    intro h
    have hx := Finset.max'_mem (thrSet ξ p) h
    simp only [thrSet, Finset.mem_filter] at hx
    exact thrJ_mem_ge_two hx.1
  rw [kminC]
  split
  · exact le_trans (by norm_num) (key _)
  · omega

lemma kminC_le_of (ξ p : ℕ) (hξ : 2 ≤ ξ) (hp : 2 ≤ p) (hpξ : p ≤ ξ)
    (hthr : ∀ j ∈ thrJ p, Fq (thrV p j) 1 ≤ Fq p j)
    (hpos : ∀ j ∈ thrJ p, 2 ≤ thrV p j) :
    ((kminC ξ p : ℝ)) ≤ muF p (Fq ξ 1) := by
  have hε : 0 < Fq ξ 1 := Fq_pos ξ hξ
  unfold muF
  rw [caMu_ge_iff_caF p (Fq ξ 1) (kminC ξ p) hp hε (one_le_kminC ξ p)]
  by_cases h : (thrSet ξ p).Nonempty
  · have hk : kminC ξ p = (thrSet ξ p).max' h := by rw [kminC, dif_pos h]
    rw [hk]
    have hmem := Finset.max'_mem (thrSet ξ p) h
    simp only [thrSet, Finset.mem_filter] at hmem
    obtain ⟨hjJ, htv⟩ := hmem
    exact le_trans (Fq_mono (hpos _ hjJ) hξ htv) (hthr _ hjJ)
  · have hk : kminC ξ p = 1 := by rw [kminC, dif_neg h]
    rw [hk]; exact Fq_mono hp hξ hpξ

lemma Fq2_eq (p : ℕ) (hp : 2 ≤ p) : Fq p 2 = Real.log (1 + 1/((p:ℝ)^2+(p:ℝ)))/Real.log (p:ℝ) := by
  unfold Fq
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have h3 : (p:ℝ)^(2+1) = (p:ℝ)^3 := by norm_num
  have hne : (p:ℝ)^3 - (p:ℝ) ≠ 0 := by
    have hlt : (p:ℝ)^1 < (p:ℝ)^3 := pow_lt_pow_right₀ hp1 (by norm_num : 1 < 3)
    have : (0:ℝ) < (p:ℝ)^3 - (p:ℝ) := by simpa [pow_one] using sub_pos.mpr hlt
    linarith
  have hne2 : (p:ℝ)^2 + (p:ℝ) ≠ 0 := by nlinarith [hp0]
  rw [h3]
  have heq : (((p:ℝ)^3-1)/((p:ℝ)^3-(p:ℝ))) = 1 + 1/((p:ℝ)^2+(p:ℝ)) := by
    rw [div_eq_iff hne]
    field_simp [hne2]; ring
  rw [heq]

lemma Fq2_le {q ξ : ℕ} (hq : 2 ≤ q) (hξ : 2 ≤ ξ) (hle : q ≤ ξ) : Fq ξ 2 ≤ Fq q 2 := by
  rw [Fq2_eq q hq, Fq2_eq ξ hξ]
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hξ0 : (0:ℝ) < (ξ:ℝ) := by exact_mod_cast (by omega : 0 < ξ)
  have hle' : (q:ℝ) ≤ (ξ:ℝ) := by exact_mod_cast hle
  have hqa : (0:ℝ) < (q:ℝ)^2+(q:ℝ) := by nlinarith [hq0]
  have hmono : (q:ℝ)^2+(q:ℝ) ≤ (ξ:ℝ)^2+(ξ:ℝ) := by nlinarith [hle', hq0]
  have hdiv : 1/((ξ:ℝ)^2+(ξ:ℝ)) ≤ 1/((q:ℝ)^2+(q:ℝ)) := one_div_le_one_div_of_le hqa hmono
  have hn : 1 + 1/((ξ:ℝ)^2+(ξ:ℝ)) ≤ 1 + 1/((q:ℝ)^2+(q:ℝ)) := by linarith
  have hlog : Real.log (1 + 1/((ξ:ℝ)^2+(ξ:ℝ))) ≤ Real.log (1 + 1/((q:ℝ)^2+(q:ℝ))) :=
    Real.log_le_log (by positivity) hn
  have hB0 : (0:ℝ) ≤ Real.log (1 + 1/((q:ℝ)^2+(q:ℝ))) := by
    apply Real.log_nonneg; have := one_div_pos.mpr hqa; linarith
  have hqlog : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hξlog : 0 < Real.log (ξ:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ξ))
  have hlelog : Real.log (q:ℝ) ≤ Real.log (ξ:ℝ) := Real.log_le_log hq0 hle'
  have e1 : Real.log (1 + 1/((ξ:ℝ)^2+(ξ:ℝ))) / Real.log (ξ:ℝ)
      ≤ Real.log (1 + 1/((q:ℝ)^2+(q:ℝ))) / Real.log (ξ:ℝ) :=
    div_le_div_of_nonneg_right hlog (le_of_lt hξlog)
  have e2 : Real.log (1 + 1/((q:ℝ)^2+(q:ℝ))) / Real.log (ξ:ℝ)
      ≤ Real.log (1 + 1/((q:ℝ)^2+(q:ℝ))) / Real.log (q:ℝ) := by
    rw [div_le_div_iff₀ hξlog hqlog]
    nlinarith [hB0, hlelog]
  linarith [e1, e2]

lemma F53b : Fq 53 2 < Fq 1531 1 := by
  apply F1_gt_F_of (by norm_num) (by norm_num) (by norm_num) (by norm_num [logDepth]) (by norm_num [logDepth])
  decide +kernel

lemma kminC_le_2 (ξ : ℕ) (hξ : 2 ≤ ξ) : ((kminC ξ 2 : ℝ)) ≤ muF 2 (Fq ξ 1) := kminC_le_of ξ 2 (by omega) (by norm_num) hξ (thrKey_2) (thrV_ge_two_2)

lemma kminC_le_3 (ξ : ℕ) (hξ : 3 ≤ ξ) : ((kminC ξ 3 : ℝ)) ≤ muF 3 (Fq ξ 1) := kminC_le_of ξ 3 (by omega) (by norm_num) hξ (thrKey_3) (thrV_ge_two_3)

lemma kminC_le_5 (ξ : ℕ) (hξ : 5 ≤ ξ) : ((kminC ξ 5 : ℝ)) ≤ muF 5 (Fq ξ 1) := kminC_le_of ξ 5 (by omega) (by norm_num) hξ (thrKey_5) (thrV_ge_two_5)

lemma kminC_le_7 (ξ : ℕ) (hξ : 7 ≤ ξ) : ((kminC ξ 7 : ℝ)) ≤ muF 7 (Fq ξ 1) := kminC_le_of ξ 7 (by omega) (by norm_num) hξ (thrKey_7) (thrV_ge_two_7)

lemma kminC_le_11 (ξ : ℕ) (hξ : 11 ≤ ξ) : ((kminC ξ 11 : ℝ)) ≤ muF 11 (Fq ξ 1) := kminC_le_of ξ 11 (by omega) (by norm_num) hξ (thrKey_11) (thrV_ge_two_11)

lemma kminC_le_13 (ξ : ℕ) (hξ : 13 ≤ ξ) : ((kminC ξ 13 : ℝ)) ≤ muF 13 (Fq ξ 1) := kminC_le_of ξ 13 (by omega) (by norm_num) hξ (thrKey_13) (thrV_ge_two_13)

lemma kminC_le_17 (ξ : ℕ) (hξ : 17 ≤ ξ) : ((kminC ξ 17 : ℝ)) ≤ muF 17 (Fq ξ 1) := kminC_le_of ξ 17 (by omega) (by norm_num) hξ (thrKey_17) (thrV_ge_two_17)

lemma kminC_le_19 (ξ : ℕ) (hξ : 19 ≤ ξ) : ((kminC ξ 19 : ℝ)) ≤ muF 19 (Fq ξ 1) := kminC_le_of ξ 19 (by omega) (by norm_num) hξ (thrKey_19) (thrV_ge_two_19)

lemma kminC_le_23 (ξ : ℕ) (hξ : 23 ≤ ξ) : ((kminC ξ 23 : ℝ)) ≤ muF 23 (Fq ξ 1) := kminC_le_of ξ 23 (by omega) (by norm_num) hξ (thrKey_23) (thrV_ge_two_23)

lemma kminC_le_29 (ξ : ℕ) (hξ : 29 ≤ ξ) : ((kminC ξ 29 : ℝ)) ≤ muF 29 (Fq ξ 1) := kminC_le_of ξ 29 (by omega) (by norm_num) hξ (thrKey_29) (thrV_ge_two_29)

lemma kminC_le_31 (ξ : ℕ) (hξ : 31 ≤ ξ) : ((kminC ξ 31 : ℝ)) ≤ muF 31 (Fq ξ 1) := kminC_le_of ξ 31 (by omega) (by norm_num) hξ (thrKey_31) (thrV_ge_two_31)

lemma kminC_le_37 (ξ : ℕ) (hξ : 37 ≤ ξ) : ((kminC ξ 37 : ℝ)) ≤ muF 37 (Fq ξ 1) := kminC_le_of ξ 37 (by omega) (by norm_num) hξ (thrKey_37) (thrV_ge_two_37)

lemma kminC_le_41 (ξ : ℕ) (hξ : 41 ≤ ξ) : ((kminC ξ 41 : ℝ)) ≤ muF 41 (Fq ξ 1) := kminC_le_of ξ 41 (by omega) (by norm_num) hξ (thrKey_41) (thrV_ge_two_41)

lemma kminC_le_43 (ξ : ℕ) (hξ : 43 ≤ ξ) : ((kminC ξ 43 : ℝ)) ≤ muF 43 (Fq ξ 1) := kminC_le_of ξ 43 (by omega) (by norm_num) hξ (thrKey_43) (thrV_ge_two_43)

lemma kminC_le_47 (ξ : ℕ) (hξ : 47 ≤ ξ) : ((kminC ξ 47 : ℝ)) ≤ muF 47 (Fq ξ 1) := kminC_le_of ξ 47 (by omega) (by norm_num) hξ (thrKey_47) (thrV_ge_two_47)

lemma kminC_le (ξ p : ℕ) (hξ : 2 ≤ ξ) (hp : Nat.Prime p) (hpξ : p ≤ ξ) :
    ((kminC ξ p : ℝ)) ≤ muF p (Fq ξ 1) := by
  by_cases h47 : p ≤ 47
  · interval_cases p

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_2 ξ hpξ

    · exact kminC_le_3 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_5 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_7 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_11 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_13 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_17 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_19 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_23 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_29 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_31 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_37 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_41 ξ hpξ

    · exfalso; revert hp; decide

    · exact kminC_le_43 ξ hpξ

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kminC_le_47 ξ hpξ

  · have hp53 : 53 ≤ p := by
      by_contra hc; push_neg at hc
      interval_cases p <;> (exfalso; revert hp; decide)
    have hempty : thrSet ξ p = ∅ := by rw [thrSet, thrJ_eq_empty_of_ge p (by omega)]; simp
    have hk : kminC ξ p = 1 := by rw [kminC, dif_neg (by rw [hempty]; exact Finset.not_nonempty_empty)]
    rw [hk]
    unfold muF
    rw [caMu_ge_iff_caF p (Fq ξ 1) 1 hp.two_le (Fq_pos ξ hξ) (by norm_num)]
    exact Fq_mono hp.two_le hξ hpξ

lemma kmaxC_ge_2 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 2 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 2 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 2 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 2 (kmaxC ξnext 2 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 2).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 2) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 2).max' h + 1 ∈ thrJ 2
      · have hnot : ¬ (thrV 2 ((thrSet ξnext 2).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 2).max' h + 1 ∈ thrSet ξnext 2 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 2) ((thrSet ξnext 2).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_2 ((thrSet ξnext 2).max' h + 1) hin
        have hspec := thrPrev_spec_2 ((thrSet ξnext 2).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 2 ((thrSet ξnext 2).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 2).max' h = thrJmax 2 := by
          have hK2 : 2 ≤ (thrSet ξnext 2).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 2).max' h ≤ thrJmax 2 := by
            have hh : (thrSet ξnext 2).max' h ∈ Finset.Icc 2 12 := by
              rw [← thrJ_eq_2]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 2 ≤ (thrSet ξnext 2).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 2).max' h < 12 := hc
            have hc' : (thrSet ξnext 2).max' h + 1 ≤ 12 := by omega
            exact hin (by rw [thrJ_eq_2]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_2) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 2
      · have hnot : ¬ (thrV 2 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_2 2 h2
        have hspec := thrPrev_spec_2 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 2 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_2, Finset.mem_Icc] at h2
        omega
  have hlt : muF 2 (Fq ξnext 1) < ((kmaxC ξnext 2 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 2 + 1 : ℕ) : ℝ) ≤ muF 2 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 2 (Fq ξnext 1) (kmaxC ξnext 2 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 2 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_3 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 3 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 3 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 3 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 3 (kmaxC ξnext 3 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 3).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 3) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 3).max' h + 1 ∈ thrJ 3
      · have hnot : ¬ (thrV 3 ((thrSet ξnext 3).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 3).max' h + 1 ∈ thrSet ξnext 3 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 3) ((thrSet ξnext 3).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_3 ((thrSet ξnext 3).max' h + 1) hin
        have hspec := thrPrev_spec_3 ((thrSet ξnext 3).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 3 ((thrSet ξnext 3).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 3).max' h = thrJmax 3 := by
          have hK2 : 2 ≤ (thrSet ξnext 3).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 3).max' h ≤ thrJmax 3 := by
            have hh : (thrSet ξnext 3).max' h ∈ Finset.Icc 2 8 := by
              rw [← thrJ_eq_3]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 3 ≤ (thrSet ξnext 3).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 3).max' h < 8 := hc
            have hc' : (thrSet ξnext 3).max' h + 1 ≤ 8 := by omega
            exact hin (by rw [thrJ_eq_3]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_3) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 3
      · have hnot : ¬ (thrV 3 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_3 2 h2
        have hspec := thrPrev_spec_3 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 3 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_3, Finset.mem_Icc] at h2
        omega
  have hlt : muF 3 (Fq ξnext 1) < ((kmaxC ξnext 3 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 3 + 1 : ℕ) : ℝ) ≤ muF 3 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 3 (Fq ξnext 1) (kmaxC ξnext 3 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 3 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_5 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 5 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 5 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 5 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 5 (kmaxC ξnext 5 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 5).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 5) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 5).max' h + 1 ∈ thrJ 5
      · have hnot : ¬ (thrV 5 ((thrSet ξnext 5).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 5).max' h + 1 ∈ thrSet ξnext 5 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 5) ((thrSet ξnext 5).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_5 ((thrSet ξnext 5).max' h + 1) hin
        have hspec := thrPrev_spec_5 ((thrSet ξnext 5).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 5 ((thrSet ξnext 5).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 5).max' h = thrJmax 5 := by
          have hK2 : 2 ≤ (thrSet ξnext 5).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 5).max' h ≤ thrJmax 5 := by
            have hh : (thrSet ξnext 5).max' h ∈ Finset.Icc 2 5 := by
              rw [← thrJ_eq_5]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 5 ≤ (thrSet ξnext 5).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 5).max' h < 5 := hc
            have hc' : (thrSet ξnext 5).max' h + 1 ≤ 5 := by omega
            exact hin (by rw [thrJ_eq_5]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_5) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 5
      · have hnot : ¬ (thrV 5 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_5 2 h2
        have hspec := thrPrev_spec_5 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 5 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_5, Finset.mem_Icc] at h2
        omega
  have hlt : muF 5 (Fq ξnext 1) < ((kmaxC ξnext 5 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 5 + 1 : ℕ) : ℝ) ≤ muF 5 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 5 (Fq ξnext 1) (kmaxC ξnext 5 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 5 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_7 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 7 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 7 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 7 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 7 (kmaxC ξnext 7 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 7).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 7) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 7).max' h + 1 ∈ thrJ 7
      · have hnot : ¬ (thrV 7 ((thrSet ξnext 7).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 7).max' h + 1 ∈ thrSet ξnext 7 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 7) ((thrSet ξnext 7).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_7 ((thrSet ξnext 7).max' h + 1) hin
        have hspec := thrPrev_spec_7 ((thrSet ξnext 7).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 7 ((thrSet ξnext 7).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 7).max' h = thrJmax 7 := by
          have hK2 : 2 ≤ (thrSet ξnext 7).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 7).max' h ≤ thrJmax 7 := by
            have hh : (thrSet ξnext 7).max' h ∈ Finset.Icc 2 4 := by
              rw [← thrJ_eq_7]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 7 ≤ (thrSet ξnext 7).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 7).max' h < 4 := hc
            have hc' : (thrSet ξnext 7).max' h + 1 ≤ 4 := by omega
            exact hin (by rw [thrJ_eq_7]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_7) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 7
      · have hnot : ¬ (thrV 7 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_7 2 h2
        have hspec := thrPrev_spec_7 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 7 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_7, Finset.mem_Icc] at h2
        omega
  have hlt : muF 7 (Fq ξnext 1) < ((kmaxC ξnext 7 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 7 + 1 : ℕ) : ℝ) ≤ muF 7 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 7 (Fq ξnext 1) (kmaxC ξnext 7 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 7 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_11 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 11 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 11 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 11 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 11 (kmaxC ξnext 11 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 11).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 11) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 11).max' h + 1 ∈ thrJ 11
      · have hnot : ¬ (thrV 11 ((thrSet ξnext 11).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 11).max' h + 1 ∈ thrSet ξnext 11 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 11) ((thrSet ξnext 11).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_11 ((thrSet ξnext 11).max' h + 1) hin
        have hspec := thrPrev_spec_11 ((thrSet ξnext 11).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 11 ((thrSet ξnext 11).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 11).max' h = thrJmax 11 := by
          have hK2 : 2 ≤ (thrSet ξnext 11).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 11).max' h ≤ thrJmax 11 := by
            have hh : (thrSet ξnext 11).max' h ∈ Finset.Icc 2 3 := by
              rw [← thrJ_eq_11]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 11 ≤ (thrSet ξnext 11).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 11).max' h < 3 := hc
            have hc' : (thrSet ξnext 11).max' h + 1 ≤ 3 := by omega
            exact hin (by rw [thrJ_eq_11]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_11) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 11
      · have hnot : ¬ (thrV 11 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_11 2 h2
        have hspec := thrPrev_spec_11 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 11 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_11, Finset.mem_Icc] at h2
        omega
  have hlt : muF 11 (Fq ξnext 1) < ((kmaxC ξnext 11 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 11 + 1 : ℕ) : ℝ) ≤ muF 11 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 11 (Fq ξnext 1) (kmaxC ξnext 11 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 11 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_13 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 13 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 13 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 13 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 13 (kmaxC ξnext 13 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 13).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 13) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 13).max' h + 1 ∈ thrJ 13
      · have hnot : ¬ (thrV 13 ((thrSet ξnext 13).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 13).max' h + 1 ∈ thrSet ξnext 13 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 13) ((thrSet ξnext 13).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_13 ((thrSet ξnext 13).max' h + 1) hin
        have hspec := thrPrev_spec_13 ((thrSet ξnext 13).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 13 ((thrSet ξnext 13).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 13).max' h = thrJmax 13 := by
          have hK2 : 2 ≤ (thrSet ξnext 13).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 13).max' h ≤ thrJmax 13 := by
            have hh : (thrSet ξnext 13).max' h ∈ Finset.Icc 2 3 := by
              rw [← thrJ_eq_13]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 13 ≤ (thrSet ξnext 13).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 13).max' h < 3 := hc
            have hc' : (thrSet ξnext 13).max' h + 1 ≤ 3 := by omega
            exact hin (by rw [thrJ_eq_13]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_13) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 13
      · have hnot : ¬ (thrV 13 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_13 2 h2
        have hspec := thrPrev_spec_13 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 13 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_13, Finset.mem_Icc] at h2
        omega
  have hlt : muF 13 (Fq ξnext 1) < ((kmaxC ξnext 13 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 13 + 1 : ℕ) : ℝ) ≤ muF 13 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 13 (Fq ξnext 1) (kmaxC ξnext 13 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 13 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_17 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 17 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 17 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 17 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 17 (kmaxC ξnext 17 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 17).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 17) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 17).max' h + 1 ∈ thrJ 17
      · have hnot : ¬ (thrV 17 ((thrSet ξnext 17).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 17).max' h + 1 ∈ thrSet ξnext 17 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 17) ((thrSet ξnext 17).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_17 ((thrSet ξnext 17).max' h + 1) hin
        have hspec := thrPrev_spec_17 ((thrSet ξnext 17).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 17 ((thrSet ξnext 17).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 17).max' h = thrJmax 17 := by
          have hK2 : 2 ≤ (thrSet ξnext 17).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 17).max' h ≤ thrJmax 17 := by
            have hh : (thrSet ξnext 17).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_17]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 17 ≤ (thrSet ξnext 17).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 17).max' h < 2 := hc
            have hc' : (thrSet ξnext 17).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_17]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_17) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 17
      · have hnot : ¬ (thrV 17 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_17 2 h2
        have hspec := thrPrev_spec_17 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 17 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_17, Finset.mem_Icc] at h2
        omega
  have hlt : muF 17 (Fq ξnext 1) < ((kmaxC ξnext 17 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 17 + 1 : ℕ) : ℝ) ≤ muF 17 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 17 (Fq ξnext 1) (kmaxC ξnext 17 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 17 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_19 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 19 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 19 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 19 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 19 (kmaxC ξnext 19 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 19).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 19) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 19).max' h + 1 ∈ thrJ 19
      · have hnot : ¬ (thrV 19 ((thrSet ξnext 19).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 19).max' h + 1 ∈ thrSet ξnext 19 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 19) ((thrSet ξnext 19).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_19 ((thrSet ξnext 19).max' h + 1) hin
        have hspec := thrPrev_spec_19 ((thrSet ξnext 19).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 19 ((thrSet ξnext 19).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 19).max' h = thrJmax 19 := by
          have hK2 : 2 ≤ (thrSet ξnext 19).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 19).max' h ≤ thrJmax 19 := by
            have hh : (thrSet ξnext 19).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_19]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 19 ≤ (thrSet ξnext 19).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 19).max' h < 2 := hc
            have hc' : (thrSet ξnext 19).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_19]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_19) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 19
      · have hnot : ¬ (thrV 19 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_19 2 h2
        have hspec := thrPrev_spec_19 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 19 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_19, Finset.mem_Icc] at h2
        omega
  have hlt : muF 19 (Fq ξnext 1) < ((kmaxC ξnext 19 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 19 + 1 : ℕ) : ℝ) ≤ muF 19 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 19 (Fq ξnext 1) (kmaxC ξnext 19 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 19 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_23 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 23 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 23 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 23 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 23 (kmaxC ξnext 23 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 23).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 23) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 23).max' h + 1 ∈ thrJ 23
      · have hnot : ¬ (thrV 23 ((thrSet ξnext 23).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 23).max' h + 1 ∈ thrSet ξnext 23 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 23) ((thrSet ξnext 23).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_23 ((thrSet ξnext 23).max' h + 1) hin
        have hspec := thrPrev_spec_23 ((thrSet ξnext 23).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 23 ((thrSet ξnext 23).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 23).max' h = thrJmax 23 := by
          have hK2 : 2 ≤ (thrSet ξnext 23).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 23).max' h ≤ thrJmax 23 := by
            have hh : (thrSet ξnext 23).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_23]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 23 ≤ (thrSet ξnext 23).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 23).max' h < 2 := hc
            have hc' : (thrSet ξnext 23).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_23]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_23) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 23
      · have hnot : ¬ (thrV 23 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_23 2 h2
        have hspec := thrPrev_spec_23 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 23 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_23, Finset.mem_Icc] at h2
        omega
  have hlt : muF 23 (Fq ξnext 1) < ((kmaxC ξnext 23 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 23 + 1 : ℕ) : ℝ) ≤ muF 23 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 23 (Fq ξnext 1) (kmaxC ξnext 23 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 23 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_29 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 29 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 29 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 29 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 29 (kmaxC ξnext 29 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 29).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 29) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 29).max' h + 1 ∈ thrJ 29
      · have hnot : ¬ (thrV 29 ((thrSet ξnext 29).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 29).max' h + 1 ∈ thrSet ξnext 29 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 29) ((thrSet ξnext 29).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_29 ((thrSet ξnext 29).max' h + 1) hin
        have hspec := thrPrev_spec_29 ((thrSet ξnext 29).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 29 ((thrSet ξnext 29).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 29).max' h = thrJmax 29 := by
          have hK2 : 2 ≤ (thrSet ξnext 29).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 29).max' h ≤ thrJmax 29 := by
            have hh : (thrSet ξnext 29).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_29]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 29 ≤ (thrSet ξnext 29).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 29).max' h < 2 := hc
            have hc' : (thrSet ξnext 29).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_29]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_29) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 29
      · have hnot : ¬ (thrV 29 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_29 2 h2
        have hspec := thrPrev_spec_29 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 29 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_29, Finset.mem_Icc] at h2
        omega
  have hlt : muF 29 (Fq ξnext 1) < ((kmaxC ξnext 29 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 29 + 1 : ℕ) : ℝ) ≤ muF 29 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 29 (Fq ξnext 1) (kmaxC ξnext 29 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 29 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_31 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 31 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 31 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 31 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 31 (kmaxC ξnext 31 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 31).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 31) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 31).max' h + 1 ∈ thrJ 31
      · have hnot : ¬ (thrV 31 ((thrSet ξnext 31).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 31).max' h + 1 ∈ thrSet ξnext 31 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 31) ((thrSet ξnext 31).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_31 ((thrSet ξnext 31).max' h + 1) hin
        have hspec := thrPrev_spec_31 ((thrSet ξnext 31).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 31 ((thrSet ξnext 31).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 31).max' h = thrJmax 31 := by
          have hK2 : 2 ≤ (thrSet ξnext 31).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 31).max' h ≤ thrJmax 31 := by
            have hh : (thrSet ξnext 31).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_31]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 31 ≤ (thrSet ξnext 31).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 31).max' h < 2 := hc
            have hc' : (thrSet ξnext 31).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_31]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_31) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 31
      · have hnot : ¬ (thrV 31 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_31 2 h2
        have hspec := thrPrev_spec_31 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 31 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_31, Finset.mem_Icc] at h2
        omega
  have hlt : muF 31 (Fq ξnext 1) < ((kmaxC ξnext 31 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 31 + 1 : ℕ) : ℝ) ≤ muF 31 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 31 (Fq ξnext 1) (kmaxC ξnext 31 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 31 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_37 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 37 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 37 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 37 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 37 (kmaxC ξnext 37 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 37).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 37) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 37).max' h + 1 ∈ thrJ 37
      · have hnot : ¬ (thrV 37 ((thrSet ξnext 37).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 37).max' h + 1 ∈ thrSet ξnext 37 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 37) ((thrSet ξnext 37).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_37 ((thrSet ξnext 37).max' h + 1) hin
        have hspec := thrPrev_spec_37 ((thrSet ξnext 37).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 37 ((thrSet ξnext 37).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 37).max' h = thrJmax 37 := by
          have hK2 : 2 ≤ (thrSet ξnext 37).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 37).max' h ≤ thrJmax 37 := by
            have hh : (thrSet ξnext 37).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_37]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 37 ≤ (thrSet ξnext 37).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 37).max' h < 2 := hc
            have hc' : (thrSet ξnext 37).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_37]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_37) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 37
      · have hnot : ¬ (thrV 37 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_37 2 h2
        have hspec := thrPrev_spec_37 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 37 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_37, Finset.mem_Icc] at h2
        omega
  have hlt : muF 37 (Fq ξnext 1) < ((kmaxC ξnext 37 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 37 + 1 : ℕ) : ℝ) ≤ muF 37 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 37 (Fq ξnext 1) (kmaxC ξnext 37 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 37 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_41 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 41 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 41 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 41 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 41 (kmaxC ξnext 41 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 41).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 41) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 41).max' h + 1 ∈ thrJ 41
      · have hnot : ¬ (thrV 41 ((thrSet ξnext 41).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 41).max' h + 1 ∈ thrSet ξnext 41 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 41) ((thrSet ξnext 41).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_41 ((thrSet ξnext 41).max' h + 1) hin
        have hspec := thrPrev_spec_41 ((thrSet ξnext 41).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 41 ((thrSet ξnext 41).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 41).max' h = thrJmax 41 := by
          have hK2 : 2 ≤ (thrSet ξnext 41).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 41).max' h ≤ thrJmax 41 := by
            have hh : (thrSet ξnext 41).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_41]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 41 ≤ (thrSet ξnext 41).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 41).max' h < 2 := hc
            have hc' : (thrSet ξnext 41).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_41]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_41) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 41
      · have hnot : ¬ (thrV 41 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_41 2 h2
        have hspec := thrPrev_spec_41 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 41 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_41, Finset.mem_Icc] at h2
        omega
  have hlt : muF 41 (Fq ξnext 1) < ((kmaxC ξnext 41 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 41 + 1 : ℕ) : ℝ) ≤ muF 41 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 41 (Fq ξnext 1) (kmaxC ξnext 41 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 41 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_43 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 43 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 43 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 43 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 43 (kmaxC ξnext 43 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 43).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 43) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 43).max' h + 1 ∈ thrJ 43
      · have hnot : ¬ (thrV 43 ((thrSet ξnext 43).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 43).max' h + 1 ∈ thrSet ξnext 43 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 43) ((thrSet ξnext 43).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_43 ((thrSet ξnext 43).max' h + 1) hin
        have hspec := thrPrev_spec_43 ((thrSet ξnext 43).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 43 ((thrSet ξnext 43).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 43).max' h = thrJmax 43 := by
          have hK2 : 2 ≤ (thrSet ξnext 43).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 43).max' h ≤ thrJmax 43 := by
            have hh : (thrSet ξnext 43).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_43]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 43 ≤ (thrSet ξnext 43).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 43).max' h < 2 := hc
            have hc' : (thrSet ξnext 43).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_43]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_43) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 43
      · have hnot : ¬ (thrV 43 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_43 2 h2
        have hspec := thrPrev_spec_43 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 43 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_43, Finset.mem_Icc] at h2
        omega
  have hlt : muF 43 (Fq ξnext 1) < ((kmaxC ξnext 43 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 43 + 1 : ℕ) : ℝ) ≤ muF 43 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 43 (Fq ξnext 1) (kmaxC ξnext 43 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 43 + 1 ≠ 0)).mpr hlt)


lemma kmaxC_ge_47 (ξnext : ℕ) (hξnext : Nat.Prime ξnext) (hgt : 47 < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF 47 (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext 47 := by
  have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
  have hmain : Fq 47 (kmaxC ξnext 47 + 1) < Fq ξnext 1 := by
    by_cases h : (thrSet ξnext 47).Nonempty
    · rw [kmaxC, dif_pos h]
      have hmem := Finset.max'_mem (thrSet ξnext 47) h
      simp only [thrSet, Finset.mem_filter] at hmem
      obtain ⟨hKJ, hKt⟩ := hmem
      by_cases hin : (thrSet ξnext 47).max' h + 1 ∈ thrJ 47
      · have hnot : ¬ (thrV 47 ((thrSet ξnext 47).max' h + 1) ≤ ξnext) := by
          intro hle
          have : (thrSet ξnext 47).max' h + 1 ∈ thrSet ξnext 47 := Finset.mem_filter.mpr ⟨hin, hle⟩
          have := Finset.le_max' (thrSet ξnext 47) ((thrSet ξnext 47).max' h + 1) this
          omega
        push_neg at hnot
        have hkey := thrKeyGtAll_47 ((thrSet ξnext 47).max' h + 1) hin
        have hspec := thrPrev_spec_47 ((thrSet ξnext 47).max' h + 1) hin
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 47 ((thrSet ξnext 47).max' h + 1) := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · have hKmax : (thrSet ξnext 47).max' h = thrJmax 47 := by
          have hK2 : 2 ≤ (thrSet ξnext 47).max' h := thrJ_mem_ge_two hKJ
          have hKle : (thrSet ξnext 47).max' h ≤ thrJmax 47 := by
            have hh : (thrSet ξnext 47).max' h ∈ Finset.Icc 2 2 := by
              rw [← thrJ_eq_47]; exact hKJ
            exact (Finset.mem_Icc.mp hh).2
          have hKgt : thrJmax 47 ≤ (thrSet ξnext 47).max' h := by
            by_contra hc
            push_neg at hc
            have hc2 : (thrSet ξnext 47).max' h < 2 := hc
            have hc' : (thrSet ξnext 47).max' h + 1 ≤ 2 := by omega
            exact hin (by rw [thrJ_eq_47]; exact Finset.mem_Icc.mpr ⟨by omega, hc'⟩)
          omega
        rw [hKmax]
        exact lt_of_lt_of_le (cut_47) (Fq_mono hξnext.two_le (by norm_num) hle1531)
    · rw [kmaxC, dif_neg h]
      by_cases h2 : (2:ℕ) ∈ thrJ 47
      · have hnot : ¬ (thrV 47 2 ≤ ξnext) := by
          intro hle; exact h ⟨2, Finset.mem_filter.mpr ⟨h2, hle⟩⟩
        push_neg at hnot
        have hkey := thrKeyGtAll_47 2 h2
        have hspec := thrPrev_spec_47 2 h2
        obtain ⟨hpq, _, hple⟩ := hspec
        have hle2 : ξnext ≤ thrPrev 47 2 := hple ξnext hξnext hnot
        exact lt_of_lt_of_le hkey (Fq_mono hξnext.two_le hpq.two_le hle2)
      · exfalso
        rw [thrJ_eq_47, Finset.mem_Icc] at h2
        omega
  have hlt : muF 47 (Fq ξnext 1) < ((kmaxC ξnext 47 + 1 : ℕ) : ℝ) := by
    by_contra hc
    have hle : ((kmaxC ξnext 47 + 1 : ℕ) : ℝ) ≤ muF 47 (Fq ξnext 1) := le_of_not_gt hc
    unfold muF at hle
    have := (caMu_ge_iff_caF 47 (Fq ξnext 1) (kmaxC ξnext 47 + 1) (by norm_num) hε (by omega)).mp hle
    exact absurd this (not_le.mpr hmain)
  exact Nat.le_of_lt_succ ((Nat.floor_lt' (by omega : kmaxC ξnext 47 + 1 ≠ 0)).mpr hlt)

lemma kmaxC_ge (ξnext p : ℕ) (hξnext : Nat.Prime ξnext) (hp : Nat.Prime p) (hgt : p < ξnext) (hle1531 : ξnext ≤ 1531) :
    ⌊muF p (Fq ξnext 1)⌋₊ ≤ kmaxC ξnext p := by
  by_cases h47 : p ≤ 47
  · interval_cases p

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_2 ξnext hξnext (by omega) hle1531

    · exact kmaxC_ge_3 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_5 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_7 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_11 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_13 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_17 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_19 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_23 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_29 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_31 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_37 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_41 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exact kmaxC_ge_43 ξnext hξnext (by omega) hle1531

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exfalso; revert hp; decide

    · exact kmaxC_ge_47 ξnext hξnext (by omega) hle1531

  · have hp53 : 53 ≤ p := by
      by_contra hc; push_neg at hc
      interval_cases p <;> (exfalso; revert hp; decide)
    have hempty : thrSet ξnext p = ∅ := by rw [thrSet, thrJ_eq_empty_of_ge p (by omega)]; simp
    have hk : kmaxC ξnext p = 1 := by rw [kmaxC, dif_neg (by rw [hempty]; exact Finset.not_nonempty_empty)]
    rw [hk]
    have hε : 0 < Fq ξnext 1 := Fq_pos ξnext hξnext.two_le
    have hmain : Fq p 2 < Fq ξnext 1 := by
      have h1 : Fq p 2 ≤ Fq 53 2 := Fq2_le (by norm_num) hp.two_le hp53
      have h2 : Fq 53 2 < Fq 1531 1 := F53b
      have h3 : Fq 1531 1 ≤ Fq ξnext 1 := Fq_mono hξnext.two_le (by norm_num) hle1531
      linarith
    have hlt : muF p (Fq ξnext 1) < ((2:ℕ):ℝ) := by
      by_contra hc
      have hle : ((2:ℕ):ℝ) ≤ muF p (Fq ξnext 1) := le_of_not_gt hc
      unfold muF at hle
      have := (caMu_ge_iff_caF p (Fq ξnext 1) 2 hp.two_le hε (by norm_num)).mp hle
      exact absurd this (not_le.mpr hmain)
    exact Nat.le_of_lt_succ ((Nat.floor_lt' (by norm_num : (2:ℕ) ≠ 0)).mpr hlt)


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

lemma gammaLo_le : ((57711/100000 : ℚ) : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hge : (57711/100000 : ℚ) ≤ gammaCert 5000 := by decide +kernel
  have hcert : ((gammaCert 5000 : ℚ) : ℝ) ≤ Real.eulerMascheroniSeq 5000 :=
    gammaCert_le_seq 5000 (by norm_num) (by norm_num [logDepth])
  have hseq : Real.eulerMascheroniSeq 5000 < Real.eulerMascheroniConstant :=
    Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 5000
  calc ((57711/100000 : ℚ) : ℝ) ≤ ((gammaCert 5000 : ℚ) : ℝ) := by exact_mod_cast hge
    _ ≤ Real.eulerMascheroniSeq 5000 := hcert
    _ ≤ Real.eulerMascheroniConstant := le_of_lt hseq

def Kcap : ℕ → ℕ

  | 2 => 12

  | 3 => 8

  | 5 => 5

  | 7 => 4

  | 11 => 3

  | 13 => 3

  | 17 => 2

  | 19 => 2

  | 23 => 2

  | 29 => 2

  | 31 => 2

  | 37 => 2

  | 41 => 2

  | 43 => 2

  | 47 => 2

  | 53 => 1

  | 59 => 1

  | 61 => 1

  | 67 => 1

  | 71 => 1

  | 73 => 1

  | 79 => 1

  | 83 => 1

  | 89 => 1

  | 97 => 1

  | 101 => 1

  | 103 => 1

  | 107 => 1

  | 109 => 1

  | 113 => 1

  | 127 => 1

  | 131 => 1

  | 137 => 1

  | 139 => 1

  | 149 => 1

  | 151 => 1

  | 157 => 1

  | 163 => 1

  | 167 => 1

  | 173 => 1

  | 179 => 1

  | 181 => 1

  | 191 => 1

  | 193 => 1

  | 197 => 1

  | 199 => 1

  | 211 => 1

  | 223 => 1

  | 227 => 1

  | 229 => 1

  | 233 => 1

  | 239 => 1

  | 241 => 1

  | 251 => 1

  | 257 => 1

  | 263 => 1

  | 269 => 1

  | 271 => 1

  | 277 => 1

  | 281 => 1

  | 283 => 1

  | 293 => 1

  | 307 => 1

  | 311 => 1

  | 313 => 1

  | 317 => 1

  | 331 => 1

  | 337 => 1

  | 347 => 1

  | 349 => 1

  | 353 => 1

  | 359 => 1

  | 367 => 1

  | 373 => 1

  | 379 => 1

  | 383 => 1

  | 389 => 1

  | 397 => 1

  | 401 => 1

  | 409 => 1

  | 419 => 1

  | 421 => 1

  | 431 => 1

  | 433 => 1

  | 439 => 1

  | 443 => 1

  | 449 => 1

  | 457 => 1

  | 461 => 1

  | 463 => 1

  | 467 => 1

  | 479 => 1

  | 487 => 1

  | 491 => 1

  | 499 => 1

  | 503 => 1

  | 509 => 1

  | 521 => 1

  | 523 => 1

  | 541 => 1

  | 547 => 1

  | 557 => 1

  | 563 => 1

  | 569 => 1

  | 571 => 1

  | 577 => 1

  | 587 => 1

  | 593 => 1

  | 599 => 1

  | 601 => 1

  | 607 => 1

  | 613 => 1

  | 617 => 1

  | 619 => 1

  | 631 => 1

  | 641 => 1

  | 643 => 1

  | 647 => 1

  | 653 => 1

  | 659 => 1

  | 661 => 1

  | 673 => 1

  | 677 => 1

  | 683 => 1

  | 691 => 1

  | 701 => 1

  | 709 => 1

  | 719 => 1

  | 727 => 1

  | 733 => 1

  | 739 => 1

  | 743 => 1

  | 751 => 1

  | 757 => 1

  | 761 => 1

  | 769 => 1

  | 773 => 1

  | 787 => 1

  | 797 => 1

  | 809 => 1

  | 811 => 1

  | 821 => 1

  | 823 => 1

  | 827 => 1

  | 829 => 1

  | 839 => 1

  | 853 => 1

  | 857 => 1

  | 859 => 1

  | 863 => 1

  | 877 => 1

  | 881 => 1

  | 883 => 1

  | 887 => 1

  | 907 => 1

  | 911 => 1

  | 919 => 1

  | 929 => 1

  | 937 => 1

  | 941 => 1

  | 947 => 1

  | 953 => 1

  | 967 => 1

  | 971 => 1

  | 977 => 1

  | 983 => 1

  | 991 => 1

  | 997 => 1

  | 1009 => 1

  | 1013 => 1

  | 1019 => 1

  | 1021 => 1

  | 1031 => 1

  | 1033 => 1

  | 1039 => 1

  | 1049 => 1

  | 1051 => 1

  | 1061 => 1

  | 1063 => 1

  | 1069 => 1

  | 1087 => 1

  | 1091 => 1

  | 1093 => 1

  | 1097 => 1

  | 1103 => 1

  | 1109 => 1

  | 1117 => 1

  | 1123 => 1

  | 1129 => 1

  | 1151 => 1

  | 1153 => 1

  | 1163 => 1

  | 1171 => 1

  | 1181 => 1

  | 1187 => 1

  | 1193 => 1

  | 1201 => 1

  | 1213 => 1

  | 1217 => 1

  | 1223 => 1

  | 1229 => 1

  | 1231 => 1

  | 1237 => 1

  | 1249 => 1

  | 1259 => 1

  | 1277 => 1

  | 1279 => 1

  | 1283 => 1

  | 1289 => 1

  | 1291 => 1

  | 1297 => 1

  | 1301 => 1

  | 1303 => 1

  | 1307 => 1

  | 1319 => 1

  | 1321 => 1

  | 1327 => 1

  | 1361 => 1

  | 1367 => 1

  | 1373 => 1

  | 1381 => 1

  | 1399 => 1

  | 1409 => 1

  | 1423 => 1

  | 1427 => 1

  | 1429 => 1

  | 1433 => 1

  | 1439 => 1

  | 1447 => 1

  | 1451 => 1

  | 1453 => 1

  | 1459 => 1

  | 1471 => 1

  | 1481 => 1

  | 1483 => 1

  | 1487 => 1

  | 1489 => 1

  | 1493 => 1

  | 1499 => 1

  | 1511 => 1

  | 1523 => 1

  | _ => 1


def inPT : ℕ → Bool := fun p => (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then true else false) else (if p ≤ 3 then (if p = 3 then true else false) else (if p = 5 then true else false))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then true else false) else (if p = 11 then true else false)) else (if p ≤ 13 then (if p = 13 then true else false) else (if p = 17 then true else false)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then true else false) else (if p = 23 then true else false)) else (if p ≤ 29 then (if p = 29 then true else false) else (if p = 31 then true else false))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then true else false) else (if p = 41 then true else false)) else (if p ≤ 43 then (if p = 43 then true else false) else (if p = 47 then true else false))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then true else false) else (if p ≤ 59 then (if p = 59 then true else false) else (if p = 61 then true else false))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then true else false) else (if p = 71 then true else false)) else (if p ≤ 73 then (if p = 73 then true else false) else (if p = 79 then true else false)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then true else false) else (if p = 89 then true else false)) else (if p ≤ 97 then (if p = 97 then true else false) else (if p = 101 then true else false))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then true else false) else (if p = 107 then true else false)) else (if p ≤ 109 then (if p = 109 then true else false) else (if p = 113 then true else false)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then true else false) else (if p ≤ 131 then (if p = 131 then true else false) else (if p = 137 then true else false))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then true else false) else (if p = 149 then true else false)) else (if p ≤ 151 then (if p = 151 then true else false) else (if p = 157 then true else false)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then true else false) else (if p = 167 then true else false)) else (if p ≤ 173 then (if p = 173 then true else false) else (if p = 179 then true else false))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then true else false) else (if p = 191 then true else false)) else (if p ≤ 193 then (if p = 193 then true else false) else (if p = 197 then true else false))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then true else false) else (if p ≤ 211 then (if p = 211 then true else false) else (if p = 223 then true else false))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then true else false) else (if p = 229 then true else false)) else (if p ≤ 233 then (if p = 233 then true else false) else (if p = 239 then true else false)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then true else false) else (if p = 251 then true else false)) else (if p ≤ 257 then (if p = 257 then true else false) else (if p = 263 then true else false))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then true else false) else (if p = 271 then true else false)) else (if p ≤ 277 then (if p = 277 then true else false) else (if p = 281 then true else false))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then true else false) else (if p ≤ 293 then (if p = 293 then true else false) else (if p = 307 then true else false))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then true else false) else (if p = 313 then true else false)) else (if p ≤ 317 then (if p = 317 then true else false) else (if p = 331 then true else false)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then true else false) else (if p = 347 then true else false)) else (if p ≤ 349 then (if p = 349 then true else false) else (if p = 353 then true else false))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then true else false) else (if p = 367 then true else false)) else (if p ≤ 373 then (if p = 373 then true else false) else (if p = 379 then true else false))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then true else false) else (if p ≤ 389 then (if p = 389 then true else false) else (if p = 397 then true else false))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then true else false) else (if p = 409 then true else false)) else (if p ≤ 419 then (if p = 419 then true else false) else (if p = 421 then true else false)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then true else false) else (if p = 433 then true else false)) else (if p ≤ 439 then (if p = 439 then true else false) else (if p = 443 then true else false))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then true else false) else (if p = 457 then true else false)) else (if p ≤ 461 then (if p = 461 then true else false) else (if p = 463 then true else false)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then true else false) else (if p ≤ 479 then (if p = 479 then true else false) else (if p = 487 then true else false))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then true else false) else (if p = 499 then true else false)) else (if p ≤ 503 then (if p = 503 then true else false) else (if p = 509 then true else false)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then true else false) else (if p = 523 then true else false)) else (if p ≤ 541 then (if p = 541 then true else false) else (if p = 547 then true else false))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then true else false) else (if p = 563 then true else false)) else (if p ≤ 569 then (if p = 569 then true else false) else (if p = 571 then true else false))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then true else false) else (if p ≤ 587 then (if p = 587 then true else false) else (if p = 593 then true else false))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then true else false) else (if p = 601 then true else false)) else (if p ≤ 607 then (if p = 607 then true else false) else (if p = 613 then true else false)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then true else false) else (if p = 619 then true else false)) else (if p ≤ 631 then (if p = 631 then true else false) else (if p = 641 then true else false))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then true else false) else (if p = 647 then true else false)) else (if p ≤ 653 then (if p = 653 then true else false) else (if p = 659 then true else false)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then true else false) else (if p ≤ 673 then (if p = 673 then true else false) else (if p = 677 then true else false))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then true else false) else (if p = 691 then true else false)) else (if p ≤ 701 then (if p = 701 then true else false) else (if p = 709 then true else false)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then true else false) else (if p = 727 then true else false)) else (if p ≤ 733 then (if p = 733 then true else false) else (if p = 739 then true else false))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then true else false) else (if p = 751 then true else false)) else (if p ≤ 757 then (if p = 757 then true else false) else (if p = 761 then true else false))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then true else false) else (if p ≤ 773 then (if p = 773 then true else false) else (if p = 787 then true else false))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then true else false) else (if p = 809 then true else false)) else (if p ≤ 811 then (if p = 811 then true else false) else (if p = 821 then true else false)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then true else false) else (if p = 827 then true else false)) else (if p ≤ 829 then (if p = 829 then true else false) else (if p = 839 then true else false))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then true else false) else (if p = 857 then true else false)) else (if p ≤ 859 then (if p = 859 then true else false) else (if p = 863 then true else false)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then true else false) else (if p ≤ 881 then (if p = 881 then true else false) else (if p = 883 then true else false))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then true else false) else (if p = 907 then true else false)) else (if p ≤ 911 then (if p = 911 then true else false) else (if p = 919 then true else false)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then true else false) else (if p = 937 then true else false)) else (if p ≤ 941 then (if p = 941 then true else false) else (if p = 947 then true else false))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then true else false) else (if p = 967 then true else false)) else (if p ≤ 971 then (if p = 971 then true else false) else (if p = 977 then true else false))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then true else false) else (if p ≤ 991 then (if p = 991 then true else false) else (if p = 997 then true else false))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then true else false) else (if p = 1013 then true else false)) else (if p ≤ 1019 then (if p = 1019 then true else false) else (if p = 1021 then true else false)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then true else false) else (if p = 1033 then true else false)) else (if p ≤ 1039 then (if p = 1039 then true else false) else (if p = 1049 then true else false))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then true else false) else (if p = 1061 then true else false)) else (if p ≤ 1063 then (if p = 1063 then true else false) else (if p = 1069 then true else false))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then true else false) else (if p ≤ 1091 then (if p = 1091 then true else false) else (if p = 1093 then true else false))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then true else false) else (if p = 1103 then true else false)) else (if p ≤ 1109 then (if p = 1109 then true else false) else (if p = 1117 then true else false)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then true else false) else (if p = 1129 then true else false)) else (if p ≤ 1151 then (if p = 1151 then true else false) else (if p = 1153 then true else false))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then true else false) else (if p = 1171 then true else false)) else (if p ≤ 1181 then (if p = 1181 then true else false) else (if p = 1187 then true else false))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then true else false) else (if p ≤ 1201 then (if p = 1201 then true else false) else (if p = 1213 then true else false))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then true else false) else (if p = 1223 then true else false)) else (if p ≤ 1229 then (if p = 1229 then true else false) else (if p = 1231 then true else false)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then true else false) else (if p = 1249 then true else false)) else (if p ≤ 1259 then (if p = 1259 then true else false) else (if p = 1277 then true else false))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then true else false) else (if p = 1283 then true else false)) else (if p ≤ 1289 then (if p = 1289 then true else false) else (if p = 1291 then true else false)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then true else false) else (if p ≤ 1301 then (if p = 1301 then true else false) else (if p = 1303 then true else false))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then true else false) else (if p = 1319 then true else false)) else (if p ≤ 1321 then (if p = 1321 then true else false) else (if p = 1327 then true else false)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then true else false) else (if p = 1367 then true else false)) else (if p ≤ 1373 then (if p = 1373 then true else false) else (if p = 1381 then true else false))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then true else false) else (if p = 1409 then true else false)) else (if p ≤ 1423 then (if p = 1423 then true else false) else (if p = 1427 then true else false))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then true else false) else (if p = 1433 then true else false)) else (if p ≤ 1439 then (if p = 1439 then true else false) else (if p = 1447 then true else false))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then true else false) else (if p = 1453 then true else false)) else (if p ≤ 1459 then (if p = 1459 then true else false) else (if p = 1471 then true else false)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then true else false) else (if p = 1483 then true else false)) else (if p ≤ 1487 then (if p = 1487 then true else false) else (if p = 1489 then true else false))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then true else false) else (if p = 1499 then true else false)) else (if p ≤ 1511 then (if p = 1511 then true else false) else (if p = 1523 then true else false)))))))))

def ubF : ℕ → ℕ → ℚ := fun p K =>
  if K = 1 then (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 405465118108/1000000000000 else 0) else (if p ≤ 3 then (if p = 3 then 287682082451/1000000000000 else 0) else (if p = 5 then 182321566793/1000000000000 else 0))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 133531402624/1000000000000 else 0) else (if p = 11 then 87011386989/1000000000000 else 0)) else (if p ≤ 13 then (if p = 13 then 74107982153/1000000000000 else 0) else (if p = 17 then 57158423839/1000000000000 else 0)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 51293304387/1000000000000 else 0) else (if p = 23 then 42559624418/1000000000000 else 0)) else (if p ≤ 29 then (if p = 29 then 33901561675/1000000000000 else 0) else (if p = 31 then 31748708314/1000000000000 else 0))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 26668257082/1000000000000 else 0) else (if p = 41 then 24097561579/1000000000000 else 0)) else (if p ≤ 43 then (if p = 43 then 22989528224/1000000000000 else 0) else (if p = 47 then 21053419197/1000000000000 else 0))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then 18692143012/1000000000000 else 0) else (if p ≤ 59 then (if p = 59 then 16807128316/1000000000000 else 0) else (if p = 61 then 16260530871/1000000000000 else 0))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then 14815095785/1000000000000 else 0) else (if p = 71 then 13986251974/1000000000000 else 0)) else (if p ≤ 73 then (if p = 73 then 13605662055/1000000000000 else 0) else (if p = 79 then 12578792206/1000000000000 else 0)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then 11976201046/1000000000000 else 0) else (if p = 89 then 11173310598/1000000000000 else 0)) else (if p ≤ 97 then (if p = 97 then 10256510167/1000000000000 else 0) else (if p = 101 then 9852306443/1000000000000 else 0))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then 9661920911/1000000000000 else 0) else (if p = 107 then 9302402662/1000000000000 else 0)) else (if p ≤ 109 then (if p = 109 then 9132493563/1000000000000 else 0) else (if p = 113 then 8810639682/1000000000000 else 0)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then 7843187461/1000000000000 else 0) else (if p ≤ 131 then (if p = 131 then 7604609385/1000000000000 else 0) else (if p = 137 then 7272769329/1000000000000 else 0))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then 7168499478/1000000000000 else 0) else (if p = 149 then 6688998150/1000000000000 else 0)) else (if p ≤ 151 then (if p = 151 then 6600694031/1000000000000 else 0) else (if p = 157 then 6349237678/1000000000000 else 0)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then 6116237017/1000000000000 else 0) else (if p = 167 then 5970176986/1000000000000 else 0)) else (if p ≤ 173 then (if p = 173 then 5763714716/1000000000000 else 0) else (if p = 179 then 5571055049/1000000000000 else 0))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then 5509665810/1000000000000 else 0) else (if p = 191 then 5221953981/1000000000000 else 0)) else (if p ≤ 193 then (if p = 193 then 5167980158/1000000000000 else 0) else (if p = 197 then 5063311956/1000000000000 else 0))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then 5012551823/1000000000000 else 0) else (if p ≤ 211 then (if p = 211 then 4728151195/1000000000000 else 0) else (if p = 223 then 4474290394/1000000000000 else 0))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then 4395621473/1000000000000 else 0) else (if p = 229 then 4357315368/1000000000000 else 0)) else (if p ≤ 233 then (if p = 233 then 4282671792/1000000000000 else 0) else (if p = 239 then 4175381410/1000000000000 else 0)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then 4140802666/1000000000000 else 0) else (if p = 251 then 3976158379/1000000000000 else 0)) else (if p ≤ 257 then (if p = 257 then 3883510026/1000000000000 else 0) else (if p = 263 then 3795080968/1000000000000 else 0))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then 3710589396/1000000000000 else 0) else (if p = 271 then 3683255416/1000000000000 else 0)) else (if p ≤ 277 then (if p = 277 then 3603617503/1000000000000 else 0) else (if p = 281 then 3552411604/1000000000000 else 0))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then 3527350517/1000000000000 else 0) else (if p ≤ 293 then (if p = 293 then 3407168321/1000000000000 else 0) else (if p = 307 then 3252045386/1000000000000 else 0))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then 3210285630/1000000000000 else 0) else (if p = 313 then 3189805368/1000000000000 else 0)) else (if p ≤ 317 then (if p = 317 then 3149618902/1000000000000 else 0) else (if p = 331 then 3016603539/1000000000000 else 0)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then 2962975130/1000000000000 else 0) else (if p = 347 then 2877709827/1000000000000 else 0)) else (if p ≤ 349 then (if p = 349 then 2861242281/1000000000000 else 0) else (if p = 353 then 2828866200/1000000000000 else 0))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then 2781652961/1000000000000 else 0) else (if p = 367 then 2721100114/1000000000000 else 0)) else (if p ≤ 373 then (if p = 373 then 2677387770/1000000000000 else 0) else (if p = 379 then 2635057638/1000000000000 else 0))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then 2607573407/1000000000000 else 0) else (if p ≤ 389 then (if p = 389 then 2567405505/1000000000000 else 0) else (if p = 397 then 2515734597/1000000000000 else 0))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then 2490671312/1000000000000 else 0) else (if p = 409 then 2442013655/1000000000000 else 0)) else (if p ≤ 419 then (if p = 419 then 2383801355/1000000000000 else 0) else (if p = 421 then 2372490353/1000000000000 else 0)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then 2317508140/1000000000000 else 0) else (if p = 433 then 2306816097/1000000000000 else 0)) else (if p ≤ 439 then (if p = 439 then 2275323837/1000000000000 else 0) else (if p = 443 then 2254802387/1000000000000 else 0))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then 2224705022/1000000000000 else 0) else (if p = 457 then 2185803219/1000000000000 else 0)) else (if p ≤ 461 then (if p = 461 then 2166858085/1000000000000 else 0) else (if p = 463 then 2157508140/1000000000000 else 0)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then 2139048248/1000000000000 else 0) else (if p ≤ 479 then (if p = 479 then 2085516491/1000000000000 else 0) else (if p = 487 then 2051292770/1000000000000 else 0))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then 2034598697/1000000000000 else 0) else (if p = 499 then 2002012670/1000000000000 else 0)) else (if p ≤ 503 then (if p = 503 then 1986107971/1000000000000 else 0) else (if p = 509 then 1962719167/1000000000000 else 0)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then 1917556129/1000000000000 else 0) else (if p = 523 then 1910230256/1000000000000 else 0)) else (if p ≤ 541 then (if p = 541 then 1846732593/1000000000000 else 0) else (if p = 547 then 1826494526/1000000000000 else 0))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then 1793732454/1000000000000 else 0) else (if p = 563 then 1774633358/1000000000000 else 0)) else (if p ≤ 569 then (if p = 569 then 1755936702/1000000000000 else 0) else (if p = 571 then 1749791723/1000000000000 else 0))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then 1731612164/1000000000000 else 0) else (if p ≤ 587 then (if p = 587 then 1702138070/1000000000000 else 0) else (if p = 593 then 1684930364/1000000000000 else 0))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then 1668067100/1000000000000 else 0) else (if p = 601 then 1662520773/1000000000000 else 0)) else (if p ≤ 607 then (if p = 607 then 1646100906/1000000000000 else 0) else (if p = 613 then 1630002210/1000000000000 else 0)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then 1619443552/1000000000000 else 0) else (if p = 619 then 1614215354/1000000000000 else 0)) else (if p ≤ 631 then (if p = 631 then 1583541605/1000000000000 else 0) else (if p = 641 then 1558856769/1000000000000 else 0))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then 1554011866/1000000000000 else 0) else (if p = 647 then 1544411851/1000000000000 else 0)) else (if p ≤ 653 then (if p = 653 then 1530232180/1000000000000 else 0) else (if p = 659 then 1516310517/1000000000000 else 0)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then 1511726085/1000000000000 else 0) else (if p ≤ 673 then (if p = 673 then 1484791267/1000000000000 else 0) else (if p = 677 then 1476025028/1000000000000 else 0))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then 1463068051/1000000000000 else 0) else (if p = 691 then 1446141849/1000000000000 else 0)) else (if p ≤ 701 then (if p = 701 then 1425526991/1000000000000 else 0) else (if p = 709 then 1409453503/1000000000000 else 0)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then 1389864289/1000000000000 else 0) else (if p = 727 then 1374580663/1000000000000 else 0)) else (if p ≤ 733 then (if p = 733 then 1363336727/1000000000000 else 0) else (if p = 739 then 1352275250/1000000000000 else 0))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then 1345000115/1000000000000 else 0) else (if p = 751 then 1330682185/1000000000000 else 0)) else (if p ≤ 757 then (if p = 757 then 1320142204/1000000000000 else 0) else (if p = 761 then 1313207824/1000000000000 else 0))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then 1299555342/1000000000000 else 0) else (if p ≤ 773 then (if p = 773 then 1292835002/1000000000000 else 0) else (if p = 787 then 1269851440/1000000000000 else 0))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then 1253928659/1000000000000 else 0) else (if p = 809 then 1235340607/1000000000000 else 0)) else (if p ≤ 811 then (if p = 811 then 1232296046/1000000000000 else 0) else (if p = 821 then 1217295603/1000000000000 else 0)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then 1214339232/1000000000000 else 0) else (if p = 827 then 1208469361/1000000000000 else 0)) else (if p ≤ 829 then (if p = 829 then 1205555655/1000000000000 else 0) else (if p = 839 then 1191195370/1000000000000 else 0))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then 1171656296/1000000000000 else 0) else (if p = 857 then 1166190890/1000000000000 else 0)) else (if p ≤ 859 then (if p = 859 then 1163477263/1000000000000 else 0) else (if p = 863 then 1158087720/1000000000000 else 0)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then 1139611262/1000000000000 else 0) else (if p ≤ 881 then (if p = 881 then 1134440070/1000000000000 else 0) else (if p = 883 then 1131872033/1000000000000 else 0))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then 1126770682/1000000000000 else 0) else (if p = 907 then 1101938486/1000000000000 else 0)) else (if p ≤ 911 then (if p = 911 then 1097102814/1000000000000 else 0) else (if p = 919 then 1087557687/1000000000000 else 0)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then 1075857333/1000000000000 else 0) else (if p = 937 then 1066676767/1000000000000 else 0)) else (if p ≤ 941 then (if p = 941 then 1062144990/1000000000000 else 0) else (if p = 947 then 1055419068/1000000000000 else 0))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then 1048777794/1000000000000 else 0) else (if p = 967 then 1033601823/1000000000000 else 0)) else (if p ≤ 971 then (if p = 971 then 1029346169/1000000000000 else 0) else (if p = 977 then 1023027992/1000000000000 else 0))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then 1016786905/1000000000000 else 0) else (if p ≤ 991 then (if p = 991 then 1008582954/1000000000000 else 0) else (if p = 997 then 1002516349/1000000000000 else 0))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then 990599481/1000000000000 else 0) else (if p = 1013 then 986689902/1000000000000 else 0)) else (if p ≤ 1019 then (if p = 1019 then 980883055/1000000000000 else 0) else (if p = 1021 then 978962598/1000000000000 else 0)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then 969472024/1000000000000 else 0) else (if p = 1033 then 967595948/1000000000000 else 0)) else (if p ≤ 1039 then (if p = 1039 then 962011036/1000000000000 else 0) else (if p = 1049 then 952844755/1000000000000 else 0))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then 951032420/1000000000000 else 0) else (if p = 1061 then 942073187/1000000000000 else 0)) else (if p ≤ 1063 then (if p = 1063 then 940301559/1000000000000 else 0) else (if p = 1069 then 935026430/1000000000000 else 0))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then 919550294/1000000000000 else 0) else (if p ≤ 1091 then (if p = 1091 then 916180471/1000000000000 else 0) else (if p = 1093 then 914504805/1000000000000 else 0))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then 911171794/1000000000000 else 0) else (if p = 1103 then 906217583/1000000000000 else 0)) else (if p ≤ 1109 then (if p = 1109 then 901316956/1000000000000 else 0) else (if p = 1117 then 894864645/1000000000000 else 0)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then 890085715/1000000000000 else 0) else (if p = 1129 then 885357556/1000000000000 else 0)) else (if p ≤ 1151 then (if p = 1151 then 868442533/1000000000000 else 0) else (if p = 1153 then 866936798/1000000000000 else 0))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then 859485772/1000000000000 else 0) else (if p = 1171 then 853616539/1000000000000 else 0)) else (if p ≤ 1181 then (if p = 1181 then 846391768/1000000000000 else 0) else (if p = 1187 then 842115312/1000000000000 else 0))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then 837881854/1000000000000 else 0) else (if p ≤ 1201 then (if p = 1201 then 832303015/1000000000000 else 0) else (if p = 1213 then 824072675/1000000000000 else 0))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then 821365282/1000000000000 else 0) else (if p = 1223 then 817337385/1000000000000 else 0)) else (if p ≤ 1229 then (if p = 1229 then 813348800/1000000000000 else 0) else (if p = 1231 then 812027909/1000000000000 else 0)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then 808090852/1000000000000 else 0) else (if p = 1249 then 800330170/1000000000000 else 0)) else (if p ≤ 1259 then (if p = 1259 then 793975901/1000000000000 else 0) else (if p = 1277 then 782788904/1000000000000 else 0))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then 781565334/1000000000000 else 0) else (if p = 1283 then 779129634/1000000000000 else 0)) else (if p ≤ 1289 then (if p = 1289 then 775504416/1000000000000 else 0) else (if p = 1291 then 774303495/1000000000000 else 0)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then 770722947/1000000000000 else 0) else (if p ≤ 1301 then (if p = 1301 then 768354256/1000000000000 else 0) else (if p = 1303 then 767175361/1000000000000 else 0))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then 764828392/1000000000000 else 0) else (if p = 1319 then 757872863/1000000000000 else 0)) else (if p ≤ 1321 then (if p = 1321 then 756725889/1000000000000 else 0) else (if p = 1327 then 753305704/1000000000000 else 0)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then 734494057/1000000000000 else 0) else (if p = 1367 then 731271458/1000000000000 else 0)) else (if p ≤ 1373 then (if p = 1373 then 728077014/1000000000000 else 0) else (if p = 1381 then 723860918/1000000000000 else 0))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then 714550937/1000000000000 else 0) else (if p = 1409 then 709481473/1000000000000 else 0)) else (if p ≤ 1423 then (if p = 1423 then 702503882/1000000000000 else 0) else (if p = 1427 then 700535422/1000000000000 else 0))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then 699555324/1000000000000 else 0) else (if p = 1433 then 697603331/1000000000000 else 0)) else (if p ≤ 1439 then (if p = 1439 then 694695682/1000000000000 else 0) else (if p = 1447 then 690856314/1000000000000 else 0))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then 688952500/1000000000000 else 0) else (if p = 1453 then 688004523/1000000000000 else 0)) else (if p ≤ 1459 then (if p = 1459 then 685176179/1000000000000 else 0) else (if p = 1471 then 679588687/1000000000000 else 0)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then 675001588/1000000000000 else 0) else (if p = 1483 then 674091589/1000000000000 else 0)) else (if p ≤ 1487 then (if p = 1487 then 672278932/1000000000000 else 0) else (if p = 1489 then 671376255/1000000000000 else 0))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then 669578153/1000000000000 else 0) else (if p = 1499 then 666898987/1000000000000 else 0)) else (if p ≤ 1511 then (if p = 1511 then 661604466/1000000000000 else 0) else (if p = 1523 then 656393351/1000000000000 else 0)))))))))
  else if K = 0 then (if inPT p then 1 else 0)
  else if inPT p then (if K = 2 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 559615797935/1000000000000 else 1) else (if p ≤ 3 then (if p = 3 then 367724790125/1000000000000 else 1) else (if p = 5 then 215111389616/1000000000000 else 1))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 151230979723/1000000000000 else 1) else (if p = 11 then 94558592625/1000000000000 else 1)) else (if p ≤ 13 then (if p = 13 then 79587447918/1000000000000 else 1) else (if p = 17 then 60421069474/1000000000000 else 1)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 53921426793/1000000000000 else 1) else (if p = 23 then 44369579664/1000000000000 else 1)) else (if p ≤ 29 then (if p = 29 then 35050326879/1000000000000 else 1) else (if p = 31 then 32756265074/1000000000000 else 1))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 27379241825/1000000000000 else 1) else (if p = 41 then 24678113119/1000000000000 else 1)) else (if p ≤ 43 then (if p = 43 then 23517929822/1000000000000 else 1) else (if p = 47 then 21496583397/1000000000000 else 1))))) else (if K = 3 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 628608669422/1000000000000 else 1) else (if p ≤ 3 then (if p = 3 then 393042598109/1000000000000 else 1) else (if p = 5 then 221542279947/1000000000000 else 1))) else (if p ≤ 7 then (if p = 7 then 153734109942/1000000000000 else 1) else (if p ≤ 11 then (if p = 11 then 95241886126/1000000000000 else 1) else (if p = 13 then 80007704280/1000000000000 else 1)))) else (if K = 4 then (if p ≤ 3 then (if p ≤ 2 then (if p = 2 then 661398492245/1000000000000 else 1) else (if p = 3 then 401341400924/1000000000000 else 1)) else (if p ≤ 5 then (if p = 5 then 222823510103/1000000000000 else 1) else (if p = 7 then 154091189038/1000000000000 else 1))) else (if K = 5 then (if p ≤ 2 then (if p = 2 then 677398833591/1000000000000 else 1) else (if p ≤ 3 then (if p = 3 then 404092434296/1000000000000 else 1) else (if p = 5 then 223079559266/1000000000000 else 1))) else (if K = 6 then (if p ≤ 2 then (if p = 2 then 685304013098/1000000000000 else 1) else (if p = 3 then 405007766167/1000000000000 else 1)) else (if K = 7 then (if p ≤ 2 then (if p = 2 then 689233291238/1000000000000 else 1) else (if p = 3 then 405312690701/1000000000000 else 1)) else (if K = 8 then (if p ≤ 2 then (if p = 2 then 691192155724/1000000000000 else 1) else (if p = 3 then 405414311554/1000000000000 else 1)) else (if K = 9 then (if p = 2 then 692170150912/1000000000000 else 1) else (if K = 10 then (if p = 2 then 692658790061/1000000000000 else 1) else (if K = 11 then (if p = 2 then 692903020127/1000000000000 else 1) else (if K = 12 then (if p = 2 then 693025112796/1000000000000 else 1) else 1)))))))))))
  else 0
def lbF : ℕ → ℚ := fun p => (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 693147170559/1000000000000 else 0) else (if p ≤ 3 then (if p = 3 then 1098612278668/1000000000000 else 0) else (if p = 5 then 1609437902434/1000000000000 else 0))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 1945910139055/1000000000000 else 0) else (if p = 11 then 2397895262798/1000000000000 else 0)) else (if p ≤ 13 then (if p = 13 then 2564949347461/1000000000000 else 0) else (if p = 17 then 2833213334056/1000000000000 else 0)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 2944438969166/1000000000000 else 0) else (if p = 23 then 3135494205929/1000000000000 else 0)) else (if p ≤ 29 then (if p = 29 then 3367295819986/1000000000000 else 0) else (if p = 31 then 3433987194485/1000000000000 else 0))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 3610917902644/1000000000000 else 0) else (if p = 41 then 3713572056704/1000000000000 else 0)) else (if p ≤ 43 then (if p = 43 then 3761200105693/1000000000000 else 0) else (if p = 47 then 3850147591710/1000000000000 else 0))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then 3970291903552/1000000000000 else 0) else (if p ≤ 59 then (if p = 59 then 4077537433905/1000000000000 else 0) else (if p = 61 then 4110873854173/1000000000000 else 0))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then 4204692609390/1000000000000 else 0) else (if p = 71 then 4262679867041/1000000000000 else 0)) else (if p ≤ 73 then (if p = 73 then 4290459431148/1000000000000 else 0) else (if p = 79 then 4369447842467/1000000000000 else 0)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then 4418840597796/1000000000000 else 0) else (if p = 89 then 4488636359732/1000000000000 else 0)) else (if p ≤ 97 then (if p = 97 then 4574710968503/1000000000000 else 0) else (if p = 101 then 4615120506841/1000000000000 else 0))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then 4634728978229/1000000000000 else 0) else (if p = 107 then 4672828824461/1000000000000 else 0)) else (if p ≤ 109 then (if p = 109 then 4691347872229/1000000000000 else 0) else (if p = 113 then 4727387808712/1000000000000 else 0)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then 4844187076458/1000000000000 else 0) else (if p ≤ 131 then (if p = 131 then 4875197313201/1000000000000 else 0) else (if p = 137 then 4919980915828/1000000000000 else 0))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then 4934473923130/1000000000000 else 0) else (if p = 149 then 5003946295945/1000000000000 else 0)) else (if p ≤ 151 then (if p = 151 then 5017279826814/1000000000000 else 0) else (if p = 157 then 5056245795348/1000000000000 else 0)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then 5093750190806/1000000000000 else 0) else (if p = 167 then 5117993802416/1000000000000 else 0)) else (if p ≤ 173 then (if p = 173 then 5153291584497/1000000000000 else 0) else (if p = 179 then 5187385795840/1000000000000 else 0))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then 5198497021265/1000000000000 else 0) else (if p = 191 then 5252273418046/1000000000000 else 0)) else (if p ≤ 193 then (if p = 193 then 5262690178904/1000000000000 else 0) else (if p = 197 then 5283203718737/1000000000000 else 0))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then 5293304814724/1000000000000 else 0) else (if p ≤ 211 then (if p = 211 then 5351858123476/1000000000000 else 0) else (if p = 223 then 5407171761460/1000000000000 else 0))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then 5424950007481/1000000000000 else 0) else (if p = 229 then 5433721993554/1000000000000 else 0)) else (if p ≤ 233 then (if p = 233 then 5451038443565/1000000000000 else 0) else (if p = 239 then 5476463541931/1000000000000 else 0)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then 5484796923490/1000000000000 else 0) else (if p = 251 then 5525452929131/1000000000000 else 0)) else (if p ≤ 257 then (if p = 257 then 5549076074895/1000000000000 else 0) else (if p = 263 then 5572154022177/1000000000000 else 0))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then 5594711369601/1000000000000 else 0) else (if p = 271 then 5602118810879/1000000000000 else 0)) else (if p ≤ 277 then (if p = 277 then 5624017496187/1000000000000 else 0) else (if p = 281 then 5638354659333/1000000000000 else 0))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then 5645446887643/1000000000000 else 0) else (if p ≤ 293 then (if p = 293 then 5680172599017/1000000000000 else 0) else (if p = 307 then 5726847737587/1000000000000 else 0))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then 5739792902179/1000000000000 else 0) else (if p = 313 then 5746203180540/1000000000000 else 0)) else (if p ≤ 317 then (if p = 317 then 5758901763877/1000000000000 else 0) else (if p = 331 then 5802118365377/1000000000000 else 0)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then 5820082920352/1000000000000 else 0) else (if p = 347 then 5849324769946/1000000000000 else 0)) else (if p ≤ 349 then (if p = 349 then 5855071912202/1000000000000 else 0) else (if p = 353 then 5866468046933/1000000000000 else 0))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then 5883322378488/1000000000000 else 0) else (if p = 367 then 5905361838054/1000000000000 else 0)) else (if p ≤ 373 then (if p = 373 then 5921578409643/1000000000000 else 0) else (if p = 379 then 5937536195082/1000000000000 else 0))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then 5948034979180/1000000000000 else 0) else (if p ≤ 389 then (if p = 389 then 5963579333618/1000000000000 else 0) else (if p = 397 then 5983936270687/1000000000000 else 0))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then 5993961417306/1000000000000 else 0) else (if p = 409 then 6013715146042/1000000000000 else 0)) else (if p ≤ 419 then (if p = 419 then 6037870909922/1000000000000 else 0) else (if p = 421 then 6042632823682/1000000000000 else 0)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then 6066108080103/1000000000000 else 0) else (if p = 433 then 6070737718002/1000000000000 else 0)) else (if p ≤ 439 then (if p = 439 then 6084499403075/1000000000000 else 0) else (if p = 443 then 6093569760045/1000000000000 else 0))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then 6107022877742/1000000000000 else 0) else (if p = 457 then 6124683380894/1000000000000 else 0)) else (if p ≤ 461 then (if p = 461 then 6133398032996/1000000000000 else 0) else (if p = 463 then 6137727044086/1000000000000 else 0)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then 6146329247668/1000000000000 else 0) else (if p ≤ 479 then (if p = 479 then 6171700587410/1000000000000 else 0) else (if p = 487 then 6188264113082/1000000000000 else 0))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then 6196444117794/1000000000000 else 0) else (if p = 499 then 6212606085751/1000000000000 else 0)) else (if p ≤ 503 then (if p = 503 then 6220590160099/1000000000000 else 0) else (if p = 509 then 6232448006550/1000000000000 else 0)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then 6255750031753/1000000000000 else 0) else (if p = 523 then 6259581454064/1000000000000 else 0)) else (if p ≤ 541 then (if p = 541 then 6293419268846/1000000000000 else 0) else (if p = 547 then 6304448792421/1000000000000 else 0))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then 6322565229927/1000000000000 else 0) else (if p = 563 then 6333279618139/1000000000000 else 0)) else (if p ≤ 569 then (if p = 569 then 6343880424126/1000000000000 else 0) else (if p = 571 then 6347389199656/1000000000000 else 0))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then 6357842256508/1000000000000 else 0) else (if p ≤ 587 then (if p = 587 then 6375024809828/1000000000000 else 0) else (if p = 593 then 6385194388997/1000000000000 else 0))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then 6395261588115/1000000000000 else 0) else (if p = 601 then 6398594924535/1000000000000 else 0)) else (if p ≤ 607 then (if p = 607 then 6408528781059/1000000000000 else 0) else (if p = 613 then 6418364925936/1000000000000 else 0)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then 6424869013905/1000000000000 else 0) else (if p = 619 then 6428105262684/1000000000000 else 0)) else (if p ≤ 631 then (if p = 631 then 6447305852541/1000000000000 else 0) else (if p = 641 then 6463029446920/1000000000000 else 0))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then 6466144714237/1000000000000 else 0) else (if p = 647 then 6472346284500/1000000000000 else 0)) else (if p ≤ 653 then (if p = 653 then 6481577119276/1000000000000 else 0) else (if p = 659 then 6490723524502/1000000000000 else 0)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then 6493753829851/1000000000000 else 0) else (if p ≤ 673 then (if p = 673 then 6511745319644/1000000000000 else 0) else (if p = 677 then 6517671262912/1000000000000 else 0))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then 6526494849570/1000000000000 else 0) else (if p = 691 then 6538139813767/1000000000000 else 0)) else (if p ≤ 701 then (if p = 701 then 6552507877034/1000000000000 else 0) else (if p = 709 then 6563855516532/1000000000000 else 0)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then 6577861347721/1000000000000 else 0) else (if p = 727 then 6588926467533/1000000000000 else 0)) else (if p ≤ 733 then (if p = 733 then 6597145691886/1000000000000 else 0) else (if p = 739 then 6605297910948/1000000000000 else 0))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then 6610696034717/1000000000000 else 0) else (if p = 751 then 6621405641764/1000000000000 else 0)) else (if p ≤ 757 then (if p = 757 then 6629363243437/1000000000000 else 0) else (if p = 761 then 6634633347861/1000000000000 else 0))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then 6645090959505/1000000000000 else 0) else (if p ≤ 773 then (if p = 773 then 6650279038587/1000000000000 else 0) else (if p = 787 then 6668228238417/1000000000000 else 0))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then 6680854668790/1000000000000 else 0) else (if p = 809 then 6695798907058/1000000000000 else 0)) else (if p ≤ 811 then (if p = 811 then 6698268044115/1000000000000 else 0) else (if p = 821 then 6710523099452/1000000000000 else 0)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then 6712956190677/1000000000000 else 0) else (if p = 827 then 6717804685023/1000000000000 else 0)) else (if p ≤ 829 then (if p = 829 then 6720220145135/1000000000000 else 0) else (if p = 839 then 6732210696467/1000000000000 else 0))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then 6748759537491/1000000000000 else 0) else (if p = 857 then 6753437908597/1000000000000 else 0)) else (if p ≤ 859 then (if p = 859 then 6755768911984/1000000000000 else 0) else (if p = 863 then 6760414681083/1000000000000 else 0)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then 6776506982372/1000000000000 else 0) else (if p ≤ 881 then (if p = 881 then 6781057615936/1000000000000 else 0) else (if p = 883 then 6783325190603/1000000000000 else 0))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then 6787844972309/1000000000000 else 0) else (if p = 907 then 6810142440115/1000000000000 else 0)) else (if p ≤ 911 then (if p = 911 then 6814542887259/1000000000000 else 0) else (if p = 919 then 6823286112355/1000000000000 else 0)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then 6834108728813/1000000000000 else 0) else (if p = 937 then 6842683272238/1000000000000 else 0)) else (if p ≤ 941 then (if p = 941 then 6846943129585/1000000000000 else 0) else (if p = 947 then 6853299083186/1000000000000 else 0))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then 6859614893654/1000000000000 else 0) else (if p = 967 then 6874198485453/1000000000000 else 0)) else (if p ≤ 971 then (if p = 971 then 6878326458291/1000000000000 else 0) else (if p = 977 then 6884486642042/1000000000000 else 0))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then 6890609110147/1000000000000 else 0) else (if p ≤ 991 then (if p = 991 then 6898714524329/1000000000000 else 0) else (if p = 997 then 6904750759961/1000000000000 else 0))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then 6916715010353/1000000000000 else 0) else (if p = 1013 then 6920671494248/1000000000000 else 0)) else (if p ≤ 1019 then (if p = 1019 then 6926577023222/1000000000000 else 0) else (if p = 1021 then 6928537808164/1000000000000 else 0)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then 6938284474016/1000000000000 else 0) else (if p = 1033 then 6940222459119/1000000000000 else 0)) else (if p ≤ 1039 then (if p = 1039 then 6946013981099/1000000000000 else 0) else (if p = 1049 then 6955592598396/1000000000000 else 0))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then 6957497360876/1000000000000 else 0) else (if p = 1061 then 6966967128613/1000000000000 else 0)) else (if p ≤ 1063 then (if p = 1063 then 6968850368341/1000000000000 else 0) else (if p = 1069 then 6974478901025/1000000000000 else 0))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then 6991176877121/1000000000000 else 0) else (if p ≤ 1091 then (if p = 1091 then 6994849975833/1000000000000 else 0) else (if p = 1093 then 6996681478176/1000000000000 else 0))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then 7000334450275/1000000000000 else 0) else (if p = 1103 then 7005789009253/1000000000000 else 0)) else (if p ≤ 1109 then (if p = 1109 then 7011213977350/1000000000000 else 0) else (if p = 1117 then 7018401789069/1000000000000 else 0)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then 7023758944738/1000000000000 else 0) else (if p = 1129 then 7029087554149/1000000000000 else 0)) else (if p ≤ 1151 then (if p = 1151 then 7048386398721/1000000000000 else 0) else (if p = 1153 then 7050122510269/1000000000000 else 0))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then 7058758142518/1000000000000 else 0) else (if p = 1171 then 7065613353597/1000000000000 else 0)) else (if p ≤ 1181 then (if p = 1181 then 7074116806197/1000000000000 else 0) else (if p = 1187 then 7079184384609/1000000000000 else 0))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then 7084226412097/1000000000000 else 0) else (if p ≤ 1201 then (if p = 1201 then 7090909812079/1000000000000 else 0) else (if p = 1213 then 7100851898944/1000000000000 else 0))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then 7104144082987/1000000000000 else 0) else (if p = 1223 then 7109062125687/1000000000000 else 0)) else (if p ≤ 1229 then (if p = 1229 then 7113956099566/1000000000000 else 0) else (if p = 1231 then 7115582116184/1000000000000 else 0)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then 7120444362392/1000000000000 else 0) else (if p = 1249 then 7130098500125/1000000000000 else 0)) else (if p ≤ 1259 then (if p = 1259 then 7138073024044/1000000000000 else 0) else (if p = 1277 then 7152268846032/1000000000000 else 0))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then 7153833791578/1000000000000 else 0) else (if p = 1283 then 7156956354615/1000000000000 else 0)) else (if p ≤ 1289 then (if p = 1289 then 7161621992939/1000000000000 else 0) else (if p = 1291 then 7163172380846/1000000000000 else 0)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then 7167809174316/1000000000000 else 0) else (if p ≤ 1301 then (if p = 1301 then 7170888468512/1000000000000 else 0) else (if p = 1303 then 7172424567124/1000000000000 else 0))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then 7175489703624/1000000000000 else 0) else (if p = 1319 then 7184629142717/1000000000000 else 0)) else (if p ≤ 1321 then (if p = 1321 then 7186144294522/1000000000000 else 0) else (if p = 1327 then 7190676024332/1000000000000 else 0)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then 7215974992651/1000000000000 else 0) else (if p = 1367 then 7220373826723/1000000000000 else 0)) else (if p ≤ 1373 then (if p = 1373 then 7224753395767/1000000000000 else 0) else (if p = 1381 then 7230563143409/1000000000000 else 0))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then 7243512964665/1000000000000 else 0) else (if p = 1409 then 7250635501898/1000000000000 else 0)) else (if p ≤ 1423 then (if p = 1423 then 7260522588089/1000000000000 else 0) else (if p = 1427 then 7263329607476/1000000000000 else 0))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then 7264730167929/1000000000000 else 0) else (if p = 1433 then 7267525417828/1000000000000 else 0)) else (if p ≤ 1439 then (if p = 1439 then 7271703696887/1000000000000 else 0) else (if p = 1447 then 7277247716631/1000000000000 else 0))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then 7280008242884/1000000000000 else 0) else (if p = 1453 then 7281385653570/1000000000000 else 0)) else (if p ≤ 1459 then (if p = 1459 then 7285506538522/1000000000000 else 0) else (if p = 1471 then 7293697710601/1000000000000 else 0)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then 7300472804267/1000000000000 else 0) else (if p = 1483 then 7301822332137/1000000000000 else 0)) else (if p ≤ 1487 then (if p = 1487 then 7304515936460/1000000000000 else 0) else (if p = 1489 then 7305860022684/1000000000000 else 0))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then 7308542787539/1000000000000 else 0) else (if p = 1499 then 7312553488102/1000000000000 else 0)) else (if p ≤ 1511 then (if p = 1511 then 7320526952272/1000000000000 else 0) else (if p = 1523 then 7328437342895/1000000000000 else 0)))))))))
def plistB : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523]


set_option maxHeartbeats 0 in
lemma ubLeafAll : ∀ (p K : ℕ), 1 ≤ K → K ≤ Kcap p → p ∈ plistB → logUpper (rq p K) ≤ ubF p K := by
  intro p K h1 h2 hp

  simp only [plistB, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with

    rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl

  all_goals (simp only [Kcap] at h2; interval_cases K <;>
    (unfold ubF logUpper logUpperAux logOneAddUpper logOneAddV logTwoUpperQ logDepth rq; decide +kernel))


set_option maxHeartbeats 0 in
lemma lbLeafAll : ∀ p, p ∈ plistB → lbF p ≤ logLower (p:ℚ) := by
  intro p hp

  simp only [plistB, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with

    rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl |     rfl

  all_goals (unfold lbF logLower logLowerAux logOneAddLower logOneAddV logTwoLowerQ logDepth; decide +kernel)

lemma one_le_kmaxC (ξnext p : ℕ) : 1 ≤ kmaxC ξnext p := by
  rw [kmaxC]
  split
  · rename_i h
    have hx := Finset.max'_mem (thrSet ξnext p) h
    simp only [thrSet, Finset.mem_filter] at hx
    exact le_trans (by norm_num : (1:ℕ) ≤ 2) (thrJ_mem_ge_two hx.1)
  · omega

set_option maxHeartbeats 0 in
lemma kmaxC_le_Kcap (ξnext p : ℕ) (hp : p ∈ plistB) : kmaxC ξnext p ≤ Kcap p := by
  have hk1 : 1 ≤ Kcap p := by unfold Kcap; split <;> omega
  by_cases h : (thrSet ξnext p).Nonempty
  · rw [kmaxC, dif_pos h]
    have hx := Finset.max'_mem (thrSet ξnext p) h
    simp only [thrSet, Finset.mem_filter] at hx
    simp only [plistB, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with

      rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl |       rfl

    · have hh := hx.1; simp only [thrJ_eq_2, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_3, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_5, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_7, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_11, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_13, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_17, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_19, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_23, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_29, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_31, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_37, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_41, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_43, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · have hh := hx.1; simp only [thrJ_eq_47, Finset.mem_Icc] at hh; simp only [Kcap]; exact hh.2

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 53 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 59 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 61 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 67 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 71 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 73 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 79 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 83 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 89 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 97 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 101 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 103 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 107 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 109 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 113 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 127 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 131 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 137 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 139 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 149 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 151 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 157 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 163 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 167 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 173 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 179 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 181 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 191 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 193 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 197 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 199 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 211 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 223 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 227 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 229 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 233 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 239 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 241 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 251 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 257 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 263 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 269 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 271 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 277 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 281 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 283 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 293 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 307 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 311 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 313 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 317 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 331 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 337 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 347 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 349 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 353 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 359 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 367 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 373 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 379 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 383 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 389 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 397 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 401 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 409 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 419 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 421 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 431 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 433 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 439 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 443 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 449 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 457 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 461 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 463 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 467 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 479 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 487 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 491 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 499 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 503 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 509 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 521 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 523 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 541 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 547 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 557 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 563 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 569 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 571 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 577 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 587 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 593 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 599 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 601 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 607 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 613 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 617 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 619 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 631 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 641 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 643 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 647 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 653 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 659 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 661 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 673 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 677 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 683 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 691 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 701 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 709 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 719 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 727 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 733 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 739 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 743 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 751 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 757 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 761 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 769 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 773 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 787 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 797 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 809 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 811 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 821 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 823 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 827 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 829 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 839 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 853 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 857 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 859 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 863 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 877 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 881 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 883 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 887 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 907 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 911 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 919 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 929 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 937 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 941 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 947 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 953 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 967 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 971 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 977 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 983 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 991 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 997 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1009 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1013 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1019 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1021 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1031 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1033 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1039 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1049 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1051 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1061 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1063 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1069 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1087 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1091 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1093 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1097 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1103 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1109 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1117 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1123 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1129 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1151 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1153 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1163 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1171 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1181 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1187 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1193 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1201 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1213 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1217 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1223 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1229 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1231 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1237 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1249 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1259 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1277 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1279 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1283 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1289 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1291 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1297 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1301 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1303 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1307 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1319 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1321 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1327 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1361 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1367 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1373 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1381 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1399 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1409 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1423 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1427 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1429 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1433 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1439 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1447 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1451 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1453 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1459 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1471 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1481 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1483 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1487 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1489 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1493 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1499 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1511 (by norm_num)] at hh; simp at hh

    · exfalso; have hh := hx.1; simp only [thrJ_eq_empty_of_ge 1523 (by norm_num)] at hh; simp at hh

  · rw [kmaxC, dif_neg h]; exact hk1

def LHSb (ξ ξnext : ℕ) : ℚ := ∑ p ∈ pfs ξ, ubF p (kmaxC ξnext p)
def ellb (ξ : ℕ) : ℚ := ∑ p ∈ pfs ξ, (kminC ξ p : ℚ) * lbF p
def RHSb (ξ : ℕ) : ℚ := logLower (max (logLower (ellb ξ)) 1)

lemma mem_plistB_of_mem_pfs {ξ p : ℕ} (hp : p ∈ pfs ξ) : p ∈ plistB := by
  have h1 : p ∈ plist.toFinset := (Finset.mem_filter.mp hp).1
  have h2 : p ∈ plist := by simpa using h1
  simpa only [plistB, plist] using h2

set_option maxHeartbeats 0 in
lemma LHSq_le_LHSb (ξ ξnext : ℕ) : LHSq ξ ξnext ≤ LHSb ξ ξnext := by
  unfold LHSq LHSb
  apply Finset.sum_le_sum
  intro p hp
  exact ubLeafAll p (kmaxC ξnext p) (one_le_kmaxC ξnext p) (kmaxC_le_Kcap ξnext p (mem_plistB_of_mem_pfs hp)) (mem_plistB_of_mem_pfs hp)

set_option maxHeartbeats 0 in
lemma ellb_le_ellq (ξ : ℕ) : ellb ξ ≤ ellq ξ := by
  unfold ellb ellq
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (lbLeafAll p (mem_plistB_of_mem_pfs hp)) (by positivity)


/-! ### Computational mirrors (List-based, cheap to reduce) -/

def plistLE (ξ : ℕ) : List ℕ := plist.filter (fun p => p ≤ ξ)

def maxD : ℕ → List ℕ → ℕ
  | d, [] => d
  | d, a :: t => max a (maxD d t)

/-- `thrLev ξ p` is the level `kminC ξ p = kmaxC ξ p` computed as a `List` fold. -/
def thrLev (ξ p : ℕ) : ℕ :=
  maxD 1 ((List.range (thrJmax p + 1)).filter (fun j => 2 ≤ j ∧ thrV p j ≤ ξ))

def LHSbL (ξ ξnext : ℕ) : ℚ := ((plistLE ξ).map (fun p => ubF p (thrLev ξnext p))).sum

def ellbL (ξ : ℕ) : ℚ := ((plistLE ξ).map (fun p => (thrLev ξ p : ℚ) * lbF p)).sum


end RobinCaFval

end Commons.NumberTheory.Robin

namespace Commons.NumberTheory.Robin.RobinCaFval
open scoped BigOperators
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 1000000

def isPrimeC (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range (p.sqrt + 1)).all (fun m => decide (¬(2 ≤ m ∧ m ∣ p)))

lemma isPrimeC_iff (p : ℕ) : isPrimeC p = true ↔ Nat.Prime p := by
  rw [Nat.prime_def_le_sqrt]
  unfold isPrimeC
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun m hm2 hms hmd => ?_⟩
    have hm : m ∈ List.range (p.sqrt + 1) := by simp only [List.mem_range]; omega
    have h := hall m hm
    rw [decide_eq_true_eq] at h
    exact h ⟨hm2, hmd⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm => ?_⟩
    rw [List.mem_range] at hm
    rw [decide_eq_true_eq]
    rintro ⟨hm2, hmd⟩
    exact h m hm2 (by omega) hmd


def nxF : ℕ → ℕ := fun xi => (if xi ≤ 659 then (if xi ≤ 281 then (if xi ≤ 113 then (if xi ≤ 47 then (if xi ≤ 17 then (if xi ≤ 5 then (if xi ≤ 2 then (if xi = 2 then 3 else 0) else (if xi ≤ 3 then (if xi = 3 then 5 else 0) else (if xi = 5 then 7 else 0))) else (if xi ≤ 11 then (if xi ≤ 7 then (if xi = 7 then 11 else 0) else (if xi = 11 then 13 else 0)) else (if xi ≤ 13 then (if xi = 13 then 17 else 0) else (if xi = 17 then 19 else 0)))) else (if xi ≤ 31 then (if xi ≤ 23 then (if xi ≤ 19 then (if xi = 19 then 23 else 0) else (if xi = 23 then 29 else 0)) else (if xi ≤ 29 then (if xi = 29 then 31 else 0) else (if xi = 31 then 37 else 0))) else (if xi ≤ 41 then (if xi ≤ 37 then (if xi = 37 then 41 else 0) else (if xi = 41 then 43 else 0)) else (if xi ≤ 43 then (if xi = 43 then 47 else 0) else (if xi = 47 then 53 else 0))))) else (if xi ≤ 79 then (if xi ≤ 61 then (if xi ≤ 53 then (if xi = 53 then 59 else 0) else (if xi ≤ 59 then (if xi = 59 then 61 else 0) else (if xi = 61 then 67 else 0))) else (if xi ≤ 71 then (if xi ≤ 67 then (if xi = 67 then 71 else 0) else (if xi = 71 then 73 else 0)) else (if xi ≤ 73 then (if xi = 73 then 79 else 0) else (if xi = 79 then 83 else 0)))) else (if xi ≤ 101 then (if xi ≤ 89 then (if xi ≤ 83 then (if xi = 83 then 89 else 0) else (if xi = 89 then 97 else 0)) else (if xi ≤ 97 then (if xi = 97 then 101 else 0) else (if xi = 101 then 103 else 0))) else (if xi ≤ 107 then (if xi ≤ 103 then (if xi = 103 then 107 else 0) else (if xi = 107 then 109 else 0)) else (if xi ≤ 109 then (if xi = 109 then 113 else 0) else (if xi = 113 then 127 else 0)))))) else (if xi ≤ 197 then (if xi ≤ 157 then (if xi ≤ 137 then (if xi ≤ 127 then (if xi = 127 then 131 else 0) else (if xi ≤ 131 then (if xi = 131 then 137 else 0) else (if xi = 137 then 139 else 0))) else (if xi ≤ 149 then (if xi ≤ 139 then (if xi = 139 then 149 else 0) else (if xi = 149 then 151 else 0)) else (if xi ≤ 151 then (if xi = 151 then 157 else 0) else (if xi = 157 then 163 else 0)))) else (if xi ≤ 179 then (if xi ≤ 167 then (if xi ≤ 163 then (if xi = 163 then 167 else 0) else (if xi = 167 then 173 else 0)) else (if xi ≤ 173 then (if xi = 173 then 179 else 0) else (if xi = 179 then 181 else 0))) else (if xi ≤ 191 then (if xi ≤ 181 then (if xi = 181 then 191 else 0) else (if xi = 191 then 193 else 0)) else (if xi ≤ 193 then (if xi = 193 then 197 else 0) else (if xi = 197 then 199 else 0))))) else (if xi ≤ 239 then (if xi ≤ 223 then (if xi ≤ 199 then (if xi = 199 then 211 else 0) else (if xi ≤ 211 then (if xi = 211 then 223 else 0) else (if xi = 223 then 227 else 0))) else (if xi ≤ 229 then (if xi ≤ 227 then (if xi = 227 then 229 else 0) else (if xi = 229 then 233 else 0)) else (if xi ≤ 233 then (if xi = 233 then 239 else 0) else (if xi = 239 then 241 else 0)))) else (if xi ≤ 263 then (if xi ≤ 251 then (if xi ≤ 241 then (if xi = 241 then 251 else 0) else (if xi = 251 then 257 else 0)) else (if xi ≤ 257 then (if xi = 257 then 263 else 0) else (if xi = 263 then 269 else 0))) else (if xi ≤ 271 then (if xi ≤ 269 then (if xi = 269 then 271 else 0) else (if xi = 271 then 277 else 0)) else (if xi ≤ 277 then (if xi = 277 then 281 else 0) else (if xi = 281 then 283 else 0))))))) else (if xi ≤ 463 then (if xi ≤ 379 then (if xi ≤ 331 then (if xi ≤ 307 then (if xi ≤ 283 then (if xi = 283 then 293 else 0) else (if xi ≤ 293 then (if xi = 293 then 307 else 0) else (if xi = 307 then 311 else 0))) else (if xi ≤ 313 then (if xi ≤ 311 then (if xi = 311 then 313 else 0) else (if xi = 313 then 317 else 0)) else (if xi ≤ 317 then (if xi = 317 then 331 else 0) else (if xi = 331 then 337 else 0)))) else (if xi ≤ 353 then (if xi ≤ 347 then (if xi ≤ 337 then (if xi = 337 then 347 else 0) else (if xi = 347 then 349 else 0)) else (if xi ≤ 349 then (if xi = 349 then 353 else 0) else (if xi = 353 then 359 else 0))) else (if xi ≤ 367 then (if xi ≤ 359 then (if xi = 359 then 367 else 0) else (if xi = 367 then 373 else 0)) else (if xi ≤ 373 then (if xi = 373 then 379 else 0) else (if xi = 379 then 383 else 0))))) else (if xi ≤ 421 then (if xi ≤ 397 then (if xi ≤ 383 then (if xi = 383 then 389 else 0) else (if xi ≤ 389 then (if xi = 389 then 397 else 0) else (if xi = 397 then 401 else 0))) else (if xi ≤ 409 then (if xi ≤ 401 then (if xi = 401 then 409 else 0) else (if xi = 409 then 419 else 0)) else (if xi ≤ 419 then (if xi = 419 then 421 else 0) else (if xi = 421 then 431 else 0)))) else (if xi ≤ 443 then (if xi ≤ 433 then (if xi ≤ 431 then (if xi = 431 then 433 else 0) else (if xi = 433 then 439 else 0)) else (if xi ≤ 439 then (if xi = 439 then 443 else 0) else (if xi = 443 then 449 else 0))) else (if xi ≤ 457 then (if xi ≤ 449 then (if xi = 449 then 457 else 0) else (if xi = 457 then 461 else 0)) else (if xi ≤ 461 then (if xi = 461 then 463 else 0) else (if xi = 463 then 467 else 0)))))) else (if xi ≤ 571 then (if xi ≤ 509 then (if xi ≤ 487 then (if xi ≤ 467 then (if xi = 467 then 479 else 0) else (if xi ≤ 479 then (if xi = 479 then 487 else 0) else (if xi = 487 then 491 else 0))) else (if xi ≤ 499 then (if xi ≤ 491 then (if xi = 491 then 499 else 0) else (if xi = 499 then 503 else 0)) else (if xi ≤ 503 then (if xi = 503 then 509 else 0) else (if xi = 509 then 521 else 0)))) else (if xi ≤ 547 then (if xi ≤ 523 then (if xi ≤ 521 then (if xi = 521 then 523 else 0) else (if xi = 523 then 541 else 0)) else (if xi ≤ 541 then (if xi = 541 then 547 else 0) else (if xi = 547 then 557 else 0))) else (if xi ≤ 563 then (if xi ≤ 557 then (if xi = 557 then 563 else 0) else (if xi = 563 then 569 else 0)) else (if xi ≤ 569 then (if xi = 569 then 571 else 0) else (if xi = 571 then 577 else 0))))) else (if xi ≤ 613 then (if xi ≤ 593 then (if xi ≤ 577 then (if xi = 577 then 587 else 0) else (if xi ≤ 587 then (if xi = 587 then 593 else 0) else (if xi = 593 then 599 else 0))) else (if xi ≤ 601 then (if xi ≤ 599 then (if xi = 599 then 601 else 0) else (if xi = 601 then 607 else 0)) else (if xi ≤ 607 then (if xi = 607 then 613 else 0) else (if xi = 613 then 617 else 0)))) else (if xi ≤ 641 then (if xi ≤ 619 then (if xi ≤ 617 then (if xi = 617 then 619 else 0) else (if xi = 619 then 631 else 0)) else (if xi ≤ 631 then (if xi = 631 then 641 else 0) else (if xi = 641 then 643 else 0))) else (if xi ≤ 647 then (if xi ≤ 643 then (if xi = 643 then 647 else 0) else (if xi = 647 then 653 else 0)) else (if xi ≤ 653 then (if xi = 653 then 659 else 0) else (if xi = 659 then 661 else 0)))))))) else (if xi ≤ 1069 then (if xi ≤ 863 then (if xi ≤ 761 then (if xi ≤ 709 then (if xi ≤ 677 then (if xi ≤ 661 then (if xi = 661 then 673 else 0) else (if xi ≤ 673 then (if xi = 673 then 677 else 0) else (if xi = 677 then 683 else 0))) else (if xi ≤ 691 then (if xi ≤ 683 then (if xi = 683 then 691 else 0) else (if xi = 691 then 701 else 0)) else (if xi ≤ 701 then (if xi = 701 then 709 else 0) else (if xi = 709 then 719 else 0)))) else (if xi ≤ 739 then (if xi ≤ 727 then (if xi ≤ 719 then (if xi = 719 then 727 else 0) else (if xi = 727 then 733 else 0)) else (if xi ≤ 733 then (if xi = 733 then 739 else 0) else (if xi = 739 then 743 else 0))) else (if xi ≤ 751 then (if xi ≤ 743 then (if xi = 743 then 751 else 0) else (if xi = 751 then 757 else 0)) else (if xi ≤ 757 then (if xi = 757 then 761 else 0) else (if xi = 761 then 769 else 0))))) else (if xi ≤ 821 then (if xi ≤ 787 then (if xi ≤ 769 then (if xi = 769 then 773 else 0) else (if xi ≤ 773 then (if xi = 773 then 787 else 0) else (if xi = 787 then 797 else 0))) else (if xi ≤ 809 then (if xi ≤ 797 then (if xi = 797 then 809 else 0) else (if xi = 809 then 811 else 0)) else (if xi ≤ 811 then (if xi = 811 then 821 else 0) else (if xi = 821 then 823 else 0)))) else (if xi ≤ 839 then (if xi ≤ 827 then (if xi ≤ 823 then (if xi = 823 then 827 else 0) else (if xi = 827 then 829 else 0)) else (if xi ≤ 829 then (if xi = 829 then 839 else 0) else (if xi = 839 then 853 else 0))) else (if xi ≤ 857 then (if xi ≤ 853 then (if xi = 853 then 857 else 0) else (if xi = 857 then 859 else 0)) else (if xi ≤ 859 then (if xi = 859 then 863 else 0) else (if xi = 863 then 877 else 0)))))) else (if xi ≤ 977 then (if xi ≤ 919 then (if xi ≤ 883 then (if xi ≤ 877 then (if xi = 877 then 881 else 0) else (if xi ≤ 881 then (if xi = 881 then 883 else 0) else (if xi = 883 then 887 else 0))) else (if xi ≤ 907 then (if xi ≤ 887 then (if xi = 887 then 907 else 0) else (if xi = 907 then 911 else 0)) else (if xi ≤ 911 then (if xi = 911 then 919 else 0) else (if xi = 919 then 929 else 0)))) else (if xi ≤ 947 then (if xi ≤ 937 then (if xi ≤ 929 then (if xi = 929 then 937 else 0) else (if xi = 937 then 941 else 0)) else (if xi ≤ 941 then (if xi = 941 then 947 else 0) else (if xi = 947 then 953 else 0))) else (if xi ≤ 967 then (if xi ≤ 953 then (if xi = 953 then 967 else 0) else (if xi = 967 then 971 else 0)) else (if xi ≤ 971 then (if xi = 971 then 977 else 0) else (if xi = 977 then 983 else 0))))) else (if xi ≤ 1021 then (if xi ≤ 997 then (if xi ≤ 983 then (if xi = 983 then 991 else 0) else (if xi ≤ 991 then (if xi = 991 then 997 else 0) else (if xi = 997 then 1009 else 0))) else (if xi ≤ 1013 then (if xi ≤ 1009 then (if xi = 1009 then 1013 else 0) else (if xi = 1013 then 1019 else 0)) else (if xi ≤ 1019 then (if xi = 1019 then 1021 else 0) else (if xi = 1021 then 1031 else 0)))) else (if xi ≤ 1049 then (if xi ≤ 1033 then (if xi ≤ 1031 then (if xi = 1031 then 1033 else 0) else (if xi = 1033 then 1039 else 0)) else (if xi ≤ 1039 then (if xi = 1039 then 1049 else 0) else (if xi = 1049 then 1051 else 0))) else (if xi ≤ 1061 then (if xi ≤ 1051 then (if xi = 1051 then 1061 else 0) else (if xi = 1061 then 1063 else 0)) else (if xi ≤ 1063 then (if xi = 1063 then 1069 else 0) else (if xi = 1069 then 1087 else 0))))))) else (if xi ≤ 1291 then (if xi ≤ 1187 then (if xi ≤ 1117 then (if xi ≤ 1093 then (if xi ≤ 1087 then (if xi = 1087 then 1091 else 0) else (if xi ≤ 1091 then (if xi = 1091 then 1093 else 0) else (if xi = 1093 then 1097 else 0))) else (if xi ≤ 1103 then (if xi ≤ 1097 then (if xi = 1097 then 1103 else 0) else (if xi = 1103 then 1109 else 0)) else (if xi ≤ 1109 then (if xi = 1109 then 1117 else 0) else (if xi = 1117 then 1123 else 0)))) else (if xi ≤ 1153 then (if xi ≤ 1129 then (if xi ≤ 1123 then (if xi = 1123 then 1129 else 0) else (if xi = 1129 then 1151 else 0)) else (if xi ≤ 1151 then (if xi = 1151 then 1153 else 0) else (if xi = 1153 then 1163 else 0))) else (if xi ≤ 1171 then (if xi ≤ 1163 then (if xi = 1163 then 1171 else 0) else (if xi = 1171 then 1181 else 0)) else (if xi ≤ 1181 then (if xi = 1181 then 1187 else 0) else (if xi = 1187 then 1193 else 0))))) else (if xi ≤ 1231 then (if xi ≤ 1213 then (if xi ≤ 1193 then (if xi = 1193 then 1201 else 0) else (if xi ≤ 1201 then (if xi = 1201 then 1213 else 0) else (if xi = 1213 then 1217 else 0))) else (if xi ≤ 1223 then (if xi ≤ 1217 then (if xi = 1217 then 1223 else 0) else (if xi = 1223 then 1229 else 0)) else (if xi ≤ 1229 then (if xi = 1229 then 1231 else 0) else (if xi = 1231 then 1237 else 0)))) else (if xi ≤ 1277 then (if xi ≤ 1249 then (if xi ≤ 1237 then (if xi = 1237 then 1249 else 0) else (if xi = 1249 then 1259 else 0)) else (if xi ≤ 1259 then (if xi = 1259 then 1277 else 0) else (if xi = 1277 then 1279 else 0))) else (if xi ≤ 1283 then (if xi ≤ 1279 then (if xi = 1279 then 1283 else 0) else (if xi = 1283 then 1289 else 0)) else (if xi ≤ 1289 then (if xi = 1289 then 1291 else 0) else (if xi = 1291 then 1297 else 0)))))) else (if xi ≤ 1427 then (if xi ≤ 1327 then (if xi ≤ 1303 then (if xi ≤ 1297 then (if xi = 1297 then 1301 else 0) else (if xi ≤ 1301 then (if xi = 1301 then 1303 else 0) else (if xi = 1303 then 1307 else 0))) else (if xi ≤ 1319 then (if xi ≤ 1307 then (if xi = 1307 then 1319 else 0) else (if xi = 1319 then 1321 else 0)) else (if xi ≤ 1321 then (if xi = 1321 then 1327 else 0) else (if xi = 1327 then 1361 else 0)))) else (if xi ≤ 1381 then (if xi ≤ 1367 then (if xi ≤ 1361 then (if xi = 1361 then 1367 else 0) else (if xi = 1367 then 1373 else 0)) else (if xi ≤ 1373 then (if xi = 1373 then 1381 else 0) else (if xi = 1381 then 1399 else 0))) else (if xi ≤ 1409 then (if xi ≤ 1399 then (if xi = 1399 then 1409 else 0) else (if xi = 1409 then 1423 else 0)) else (if xi ≤ 1423 then (if xi = 1423 then 1427 else 0) else (if xi = 1427 then 1429 else 0))))) else (if xi ≤ 1471 then (if xi ≤ 1447 then (if xi ≤ 1433 then (if xi ≤ 1429 then (if xi = 1429 then 1433 else 0) else (if xi = 1433 then 1439 else 0)) else (if xi ≤ 1439 then (if xi = 1439 then 1447 else 0) else (if xi = 1447 then 1451 else 0))) else (if xi ≤ 1453 then (if xi ≤ 1451 then (if xi = 1451 then 1453 else 0) else (if xi = 1453 then 1459 else 0)) else (if xi ≤ 1459 then (if xi = 1459 then 1471 else 0) else (if xi = 1471 then 1481 else 0)))) else (if xi ≤ 1489 then (if xi ≤ 1483 then (if xi ≤ 1481 then (if xi = 1481 then 1483 else 0) else (if xi = 1483 then 1487 else 0)) else (if xi ≤ 1487 then (if xi = 1487 then 1489 else 0) else (if xi = 1489 then 1493 else 0))) else (if xi ≤ 1499 then (if xi ≤ 1493 then (if xi = 1493 then 1499 else 0) else (if xi = 1499 then 1511 else 0)) else (if xi ≤ 1511 then (if xi = 1511 then 1523 else 0) else (if xi = 1523 then 1531 else 0)))))))))


def ubNon : ℕ → ℕ → ℕ := fun p K =>
  if K = 1 then (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 405465118108 else 0) else (if p ≤ 3 then (if p = 3 then 287682082451 else 0) else (if p = 5 then 182321566793 else 0))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 133531402624 else 0) else (if p = 11 then 87011386989 else 0)) else (if p ≤ 13 then (if p = 13 then 74107982153 else 0) else (if p = 17 then 57158423839 else 0)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 51293304387 else 0) else (if p = 23 then 42559624418 else 0)) else (if p ≤ 29 then (if p = 29 then 33901561675 else 0) else (if p = 31 then 31748708314 else 0))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 26668257082 else 0) else (if p = 41 then 24097561579 else 0)) else (if p ≤ 43 then (if p = 43 then 22989528224 else 0) else (if p = 47 then 21053419197 else 0))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then 18692143012 else 0) else (if p ≤ 59 then (if p = 59 then 16807128316 else 0) else (if p = 61 then 16260530871 else 0))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then 14815095785 else 0) else (if p = 71 then 13986251974 else 0)) else (if p ≤ 73 then (if p = 73 then 13605662055 else 0) else (if p = 79 then 12578792206 else 0)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then 11976201046 else 0) else (if p = 89 then 11173310598 else 0)) else (if p ≤ 97 then (if p = 97 then 10256510167 else 0) else (if p = 101 then 9852306443 else 0))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then 9661920911 else 0) else (if p = 107 then 9302402662 else 0)) else (if p ≤ 109 then (if p = 109 then 9132493563 else 0) else (if p = 113 then 8810639682 else 0)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then 7843187461 else 0) else (if p ≤ 131 then (if p = 131 then 7604609385 else 0) else (if p = 137 then 7272769329 else 0))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then 7168499478 else 0) else (if p = 149 then 6688998150 else 0)) else (if p ≤ 151 then (if p = 151 then 6600694031 else 0) else (if p = 157 then 6349237678 else 0)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then 6116237017 else 0) else (if p = 167 then 5970176986 else 0)) else (if p ≤ 173 then (if p = 173 then 5763714716 else 0) else (if p = 179 then 5571055049 else 0))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then 5509665810 else 0) else (if p = 191 then 5221953981 else 0)) else (if p ≤ 193 then (if p = 193 then 5167980158 else 0) else (if p = 197 then 5063311956 else 0))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then 5012551823 else 0) else (if p ≤ 211 then (if p = 211 then 4728151195 else 0) else (if p = 223 then 4474290394 else 0))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then 4395621473 else 0) else (if p = 229 then 4357315368 else 0)) else (if p ≤ 233 then (if p = 233 then 4282671792 else 0) else (if p = 239 then 4175381410 else 0)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then 4140802666 else 0) else (if p = 251 then 3976158379 else 0)) else (if p ≤ 257 then (if p = 257 then 3883510026 else 0) else (if p = 263 then 3795080968 else 0))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then 3710589396 else 0) else (if p = 271 then 3683255416 else 0)) else (if p ≤ 277 then (if p = 277 then 3603617503 else 0) else (if p = 281 then 3552411604 else 0))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then 3527350517 else 0) else (if p ≤ 293 then (if p = 293 then 3407168321 else 0) else (if p = 307 then 3252045386 else 0))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then 3210285630 else 0) else (if p = 313 then 3189805368 else 0)) else (if p ≤ 317 then (if p = 317 then 3149618902 else 0) else (if p = 331 then 3016603539 else 0)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then 2962975130 else 0) else (if p = 347 then 2877709827 else 0)) else (if p ≤ 349 then (if p = 349 then 2861242281 else 0) else (if p = 353 then 2828866200 else 0))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then 2781652961 else 0) else (if p = 367 then 2721100114 else 0)) else (if p ≤ 373 then (if p = 373 then 2677387770 else 0) else (if p = 379 then 2635057638 else 0))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then 2607573407 else 0) else (if p ≤ 389 then (if p = 389 then 2567405505 else 0) else (if p = 397 then 2515734597 else 0))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then 2490671312 else 0) else (if p = 409 then 2442013655 else 0)) else (if p ≤ 419 then (if p = 419 then 2383801355 else 0) else (if p = 421 then 2372490353 else 0)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then 2317508140 else 0) else (if p = 433 then 2306816097 else 0)) else (if p ≤ 439 then (if p = 439 then 2275323837 else 0) else (if p = 443 then 2254802387 else 0))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then 2224705022 else 0) else (if p = 457 then 2185803219 else 0)) else (if p ≤ 461 then (if p = 461 then 2166858085 else 0) else (if p = 463 then 2157508140 else 0)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then 2139048248 else 0) else (if p ≤ 479 then (if p = 479 then 2085516491 else 0) else (if p = 487 then 2051292770 else 0))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then 2034598697 else 0) else (if p = 499 then 2002012670 else 0)) else (if p ≤ 503 then (if p = 503 then 1986107971 else 0) else (if p = 509 then 1962719167 else 0)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then 1917556129 else 0) else (if p = 523 then 1910230256 else 0)) else (if p ≤ 541 then (if p = 541 then 1846732593 else 0) else (if p = 547 then 1826494526 else 0))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then 1793732454 else 0) else (if p = 563 then 1774633358 else 0)) else (if p ≤ 569 then (if p = 569 then 1755936702 else 0) else (if p = 571 then 1749791723 else 0))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then 1731612164 else 0) else (if p ≤ 587 then (if p = 587 then 1702138070 else 0) else (if p = 593 then 1684930364 else 0))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then 1668067100 else 0) else (if p = 601 then 1662520773 else 0)) else (if p ≤ 607 then (if p = 607 then 1646100906 else 0) else (if p = 613 then 1630002210 else 0)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then 1619443552 else 0) else (if p = 619 then 1614215354 else 0)) else (if p ≤ 631 then (if p = 631 then 1583541605 else 0) else (if p = 641 then 1558856769 else 0))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then 1554011866 else 0) else (if p = 647 then 1544411851 else 0)) else (if p ≤ 653 then (if p = 653 then 1530232180 else 0) else (if p = 659 then 1516310517 else 0)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then 1511726085 else 0) else (if p ≤ 673 then (if p = 673 then 1484791267 else 0) else (if p = 677 then 1476025028 else 0))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then 1463068051 else 0) else (if p = 691 then 1446141849 else 0)) else (if p ≤ 701 then (if p = 701 then 1425526991 else 0) else (if p = 709 then 1409453503 else 0)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then 1389864289 else 0) else (if p = 727 then 1374580663 else 0)) else (if p ≤ 733 then (if p = 733 then 1363336727 else 0) else (if p = 739 then 1352275250 else 0))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then 1345000115 else 0) else (if p = 751 then 1330682185 else 0)) else (if p ≤ 757 then (if p = 757 then 1320142204 else 0) else (if p = 761 then 1313207824 else 0))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then 1299555342 else 0) else (if p ≤ 773 then (if p = 773 then 1292835002 else 0) else (if p = 787 then 1269851440 else 0))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then 1253928659 else 0) else (if p = 809 then 1235340607 else 0)) else (if p ≤ 811 then (if p = 811 then 1232296046 else 0) else (if p = 821 then 1217295603 else 0)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then 1214339232 else 0) else (if p = 827 then 1208469361 else 0)) else (if p ≤ 829 then (if p = 829 then 1205555655 else 0) else (if p = 839 then 1191195370 else 0))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then 1171656296 else 0) else (if p = 857 then 1166190890 else 0)) else (if p ≤ 859 then (if p = 859 then 1163477263 else 0) else (if p = 863 then 1158087720 else 0)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then 1139611262 else 0) else (if p ≤ 881 then (if p = 881 then 1134440070 else 0) else (if p = 883 then 1131872033 else 0))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then 1126770682 else 0) else (if p = 907 then 1101938486 else 0)) else (if p ≤ 911 then (if p = 911 then 1097102814 else 0) else (if p = 919 then 1087557687 else 0)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then 1075857333 else 0) else (if p = 937 then 1066676767 else 0)) else (if p ≤ 941 then (if p = 941 then 1062144990 else 0) else (if p = 947 then 1055419068 else 0))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then 1048777794 else 0) else (if p = 967 then 1033601823 else 0)) else (if p ≤ 971 then (if p = 971 then 1029346169 else 0) else (if p = 977 then 1023027992 else 0))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then 1016786905 else 0) else (if p ≤ 991 then (if p = 991 then 1008582954 else 0) else (if p = 997 then 1002516349 else 0))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then 990599481 else 0) else (if p = 1013 then 986689902 else 0)) else (if p ≤ 1019 then (if p = 1019 then 980883055 else 0) else (if p = 1021 then 978962598 else 0)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then 969472024 else 0) else (if p = 1033 then 967595948 else 0)) else (if p ≤ 1039 then (if p = 1039 then 962011036 else 0) else (if p = 1049 then 952844755 else 0))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then 951032420 else 0) else (if p = 1061 then 942073187 else 0)) else (if p ≤ 1063 then (if p = 1063 then 940301559 else 0) else (if p = 1069 then 935026430 else 0))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then 919550294 else 0) else (if p ≤ 1091 then (if p = 1091 then 916180471 else 0) else (if p = 1093 then 914504805 else 0))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then 911171794 else 0) else (if p = 1103 then 906217583 else 0)) else (if p ≤ 1109 then (if p = 1109 then 901316956 else 0) else (if p = 1117 then 894864645 else 0)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then 890085715 else 0) else (if p = 1129 then 885357556 else 0)) else (if p ≤ 1151 then (if p = 1151 then 868442533 else 0) else (if p = 1153 then 866936798 else 0))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then 859485772 else 0) else (if p = 1171 then 853616539 else 0)) else (if p ≤ 1181 then (if p = 1181 then 846391768 else 0) else (if p = 1187 then 842115312 else 0))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then 837881854 else 0) else (if p ≤ 1201 then (if p = 1201 then 832303015 else 0) else (if p = 1213 then 824072675 else 0))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then 821365282 else 0) else (if p = 1223 then 817337385 else 0)) else (if p ≤ 1229 then (if p = 1229 then 813348800 else 0) else (if p = 1231 then 812027909 else 0)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then 808090852 else 0) else (if p = 1249 then 800330170 else 0)) else (if p ≤ 1259 then (if p = 1259 then 793975901 else 0) else (if p = 1277 then 782788904 else 0))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then 781565334 else 0) else (if p = 1283 then 779129634 else 0)) else (if p ≤ 1289 then (if p = 1289 then 775504416 else 0) else (if p = 1291 then 774303495 else 0)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then 770722947 else 0) else (if p ≤ 1301 then (if p = 1301 then 768354256 else 0) else (if p = 1303 then 767175361 else 0))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then 764828392 else 0) else (if p = 1319 then 757872863 else 0)) else (if p ≤ 1321 then (if p = 1321 then 756725889 else 0) else (if p = 1327 then 753305704 else 0)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then 734494057 else 0) else (if p = 1367 then 731271458 else 0)) else (if p ≤ 1373 then (if p = 1373 then 728077014 else 0) else (if p = 1381 then 723860918 else 0))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then 714550937 else 0) else (if p = 1409 then 709481473 else 0)) else (if p ≤ 1423 then (if p = 1423 then 702503882 else 0) else (if p = 1427 then 700535422 else 0))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then 699555324 else 0) else (if p = 1433 then 697603331 else 0)) else (if p ≤ 1439 then (if p = 1439 then 694695682 else 0) else (if p = 1447 then 690856314 else 0))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then 688952500 else 0) else (if p = 1453 then 688004523 else 0)) else (if p ≤ 1459 then (if p = 1459 then 685176179 else 0) else (if p = 1471 then 679588687 else 0)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then 675001588 else 0) else (if p = 1483 then 674091589 else 0)) else (if p ≤ 1487 then (if p = 1487 then 672278932 else 0) else (if p = 1489 then 671376255 else 0))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then 669578153 else 0) else (if p = 1499 then 666898987 else 0)) else (if p ≤ 1511 then (if p = 1511 then 661604466 else 0) else (if p = 1523 then 656393351 else 0)))))))))
  else if K = 0 then (if (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then true else false) else (if p ≤ 3 then (if p = 3 then true else false) else (if p = 5 then true else false))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then true else false) else (if p = 11 then true else false)) else (if p ≤ 13 then (if p = 13 then true else false) else (if p = 17 then true else false)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then true else false) else (if p = 23 then true else false)) else (if p ≤ 29 then (if p = 29 then true else false) else (if p = 31 then true else false))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then true else false) else (if p = 41 then true else false)) else (if p ≤ 43 then (if p = 43 then true else false) else (if p = 47 then true else false))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then true else false) else (if p ≤ 59 then (if p = 59 then true else false) else (if p = 61 then true else false))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then true else false) else (if p = 71 then true else false)) else (if p ≤ 73 then (if p = 73 then true else false) else (if p = 79 then true else false)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then true else false) else (if p = 89 then true else false)) else (if p ≤ 97 then (if p = 97 then true else false) else (if p = 101 then true else false))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then true else false) else (if p = 107 then true else false)) else (if p ≤ 109 then (if p = 109 then true else false) else (if p = 113 then true else false)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then true else false) else (if p ≤ 131 then (if p = 131 then true else false) else (if p = 137 then true else false))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then true else false) else (if p = 149 then true else false)) else (if p ≤ 151 then (if p = 151 then true else false) else (if p = 157 then true else false)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then true else false) else (if p = 167 then true else false)) else (if p ≤ 173 then (if p = 173 then true else false) else (if p = 179 then true else false))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then true else false) else (if p = 191 then true else false)) else (if p ≤ 193 then (if p = 193 then true else false) else (if p = 197 then true else false))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then true else false) else (if p ≤ 211 then (if p = 211 then true else false) else (if p = 223 then true else false))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then true else false) else (if p = 229 then true else false)) else (if p ≤ 233 then (if p = 233 then true else false) else (if p = 239 then true else false)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then true else false) else (if p = 251 then true else false)) else (if p ≤ 257 then (if p = 257 then true else false) else (if p = 263 then true else false))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then true else false) else (if p = 271 then true else false)) else (if p ≤ 277 then (if p = 277 then true else false) else (if p = 281 then true else false))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then true else false) else (if p ≤ 293 then (if p = 293 then true else false) else (if p = 307 then true else false))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then true else false) else (if p = 313 then true else false)) else (if p ≤ 317 then (if p = 317 then true else false) else (if p = 331 then true else false)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then true else false) else (if p = 347 then true else false)) else (if p ≤ 349 then (if p = 349 then true else false) else (if p = 353 then true else false))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then true else false) else (if p = 367 then true else false)) else (if p ≤ 373 then (if p = 373 then true else false) else (if p = 379 then true else false))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then true else false) else (if p ≤ 389 then (if p = 389 then true else false) else (if p = 397 then true else false))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then true else false) else (if p = 409 then true else false)) else (if p ≤ 419 then (if p = 419 then true else false) else (if p = 421 then true else false)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then true else false) else (if p = 433 then true else false)) else (if p ≤ 439 then (if p = 439 then true else false) else (if p = 443 then true else false))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then true else false) else (if p = 457 then true else false)) else (if p ≤ 461 then (if p = 461 then true else false) else (if p = 463 then true else false)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then true else false) else (if p ≤ 479 then (if p = 479 then true else false) else (if p = 487 then true else false))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then true else false) else (if p = 499 then true else false)) else (if p ≤ 503 then (if p = 503 then true else false) else (if p = 509 then true else false)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then true else false) else (if p = 523 then true else false)) else (if p ≤ 541 then (if p = 541 then true else false) else (if p = 547 then true else false))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then true else false) else (if p = 563 then true else false)) else (if p ≤ 569 then (if p = 569 then true else false) else (if p = 571 then true else false))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then true else false) else (if p ≤ 587 then (if p = 587 then true else false) else (if p = 593 then true else false))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then true else false) else (if p = 601 then true else false)) else (if p ≤ 607 then (if p = 607 then true else false) else (if p = 613 then true else false)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then true else false) else (if p = 619 then true else false)) else (if p ≤ 631 then (if p = 631 then true else false) else (if p = 641 then true else false))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then true else false) else (if p = 647 then true else false)) else (if p ≤ 653 then (if p = 653 then true else false) else (if p = 659 then true else false)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then true else false) else (if p ≤ 673 then (if p = 673 then true else false) else (if p = 677 then true else false))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then true else false) else (if p = 691 then true else false)) else (if p ≤ 701 then (if p = 701 then true else false) else (if p = 709 then true else false)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then true else false) else (if p = 727 then true else false)) else (if p ≤ 733 then (if p = 733 then true else false) else (if p = 739 then true else false))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then true else false) else (if p = 751 then true else false)) else (if p ≤ 757 then (if p = 757 then true else false) else (if p = 761 then true else false))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then true else false) else (if p ≤ 773 then (if p = 773 then true else false) else (if p = 787 then true else false))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then true else false) else (if p = 809 then true else false)) else (if p ≤ 811 then (if p = 811 then true else false) else (if p = 821 then true else false)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then true else false) else (if p = 827 then true else false)) else (if p ≤ 829 then (if p = 829 then true else false) else (if p = 839 then true else false))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then true else false) else (if p = 857 then true else false)) else (if p ≤ 859 then (if p = 859 then true else false) else (if p = 863 then true else false)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then true else false) else (if p ≤ 881 then (if p = 881 then true else false) else (if p = 883 then true else false))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then true else false) else (if p = 907 then true else false)) else (if p ≤ 911 then (if p = 911 then true else false) else (if p = 919 then true else false)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then true else false) else (if p = 937 then true else false)) else (if p ≤ 941 then (if p = 941 then true else false) else (if p = 947 then true else false))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then true else false) else (if p = 967 then true else false)) else (if p ≤ 971 then (if p = 971 then true else false) else (if p = 977 then true else false))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then true else false) else (if p ≤ 991 then (if p = 991 then true else false) else (if p = 997 then true else false))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then true else false) else (if p = 1013 then true else false)) else (if p ≤ 1019 then (if p = 1019 then true else false) else (if p = 1021 then true else false)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then true else false) else (if p = 1033 then true else false)) else (if p ≤ 1039 then (if p = 1039 then true else false) else (if p = 1049 then true else false))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then true else false) else (if p = 1061 then true else false)) else (if p ≤ 1063 then (if p = 1063 then true else false) else (if p = 1069 then true else false))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then true else false) else (if p ≤ 1091 then (if p = 1091 then true else false) else (if p = 1093 then true else false))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then true else false) else (if p = 1103 then true else false)) else (if p ≤ 1109 then (if p = 1109 then true else false) else (if p = 1117 then true else false)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then true else false) else (if p = 1129 then true else false)) else (if p ≤ 1151 then (if p = 1151 then true else false) else (if p = 1153 then true else false))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then true else false) else (if p = 1171 then true else false)) else (if p ≤ 1181 then (if p = 1181 then true else false) else (if p = 1187 then true else false))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then true else false) else (if p ≤ 1201 then (if p = 1201 then true else false) else (if p = 1213 then true else false))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then true else false) else (if p = 1223 then true else false)) else (if p ≤ 1229 then (if p = 1229 then true else false) else (if p = 1231 then true else false)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then true else false) else (if p = 1249 then true else false)) else (if p ≤ 1259 then (if p = 1259 then true else false) else (if p = 1277 then true else false))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then true else false) else (if p = 1283 then true else false)) else (if p ≤ 1289 then (if p = 1289 then true else false) else (if p = 1291 then true else false)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then true else false) else (if p ≤ 1301 then (if p = 1301 then true else false) else (if p = 1303 then true else false))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then true else false) else (if p = 1319 then true else false)) else (if p ≤ 1321 then (if p = 1321 then true else false) else (if p = 1327 then true else false)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then true else false) else (if p = 1367 then true else false)) else (if p ≤ 1373 then (if p = 1373 then true else false) else (if p = 1381 then true else false))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then true else false) else (if p = 1409 then true else false)) else (if p ≤ 1423 then (if p = 1423 then true else false) else (if p = 1427 then true else false))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then true else false) else (if p = 1433 then true else false)) else (if p ≤ 1439 then (if p = 1439 then true else false) else (if p = 1447 then true else false))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then true else false) else (if p = 1453 then true else false)) else (if p ≤ 1459 then (if p = 1459 then true else false) else (if p = 1471 then true else false)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then true else false) else (if p = 1483 then true else false)) else (if p ≤ 1487 then (if p = 1487 then true else false) else (if p = 1489 then true else false))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then true else false) else (if p = 1499 then true else false)) else (if p ≤ 1511 then (if p = 1511 then true else false) else (if p = 1523 then true else false))))))))) then 1000000000000 else 0)
  else if (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then true else false) else (if p ≤ 3 then (if p = 3 then true else false) else (if p = 5 then true else false))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then true else false) else (if p = 11 then true else false)) else (if p ≤ 13 then (if p = 13 then true else false) else (if p = 17 then true else false)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then true else false) else (if p = 23 then true else false)) else (if p ≤ 29 then (if p = 29 then true else false) else (if p = 31 then true else false))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then true else false) else (if p = 41 then true else false)) else (if p ≤ 43 then (if p = 43 then true else false) else (if p = 47 then true else false))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then true else false) else (if p ≤ 59 then (if p = 59 then true else false) else (if p = 61 then true else false))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then true else false) else (if p = 71 then true else false)) else (if p ≤ 73 then (if p = 73 then true else false) else (if p = 79 then true else false)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then true else false) else (if p = 89 then true else false)) else (if p ≤ 97 then (if p = 97 then true else false) else (if p = 101 then true else false))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then true else false) else (if p = 107 then true else false)) else (if p ≤ 109 then (if p = 109 then true else false) else (if p = 113 then true else false)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then true else false) else (if p ≤ 131 then (if p = 131 then true else false) else (if p = 137 then true else false))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then true else false) else (if p = 149 then true else false)) else (if p ≤ 151 then (if p = 151 then true else false) else (if p = 157 then true else false)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then true else false) else (if p = 167 then true else false)) else (if p ≤ 173 then (if p = 173 then true else false) else (if p = 179 then true else false))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then true else false) else (if p = 191 then true else false)) else (if p ≤ 193 then (if p = 193 then true else false) else (if p = 197 then true else false))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then true else false) else (if p ≤ 211 then (if p = 211 then true else false) else (if p = 223 then true else false))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then true else false) else (if p = 229 then true else false)) else (if p ≤ 233 then (if p = 233 then true else false) else (if p = 239 then true else false)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then true else false) else (if p = 251 then true else false)) else (if p ≤ 257 then (if p = 257 then true else false) else (if p = 263 then true else false))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then true else false) else (if p = 271 then true else false)) else (if p ≤ 277 then (if p = 277 then true else false) else (if p = 281 then true else false))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then true else false) else (if p ≤ 293 then (if p = 293 then true else false) else (if p = 307 then true else false))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then true else false) else (if p = 313 then true else false)) else (if p ≤ 317 then (if p = 317 then true else false) else (if p = 331 then true else false)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then true else false) else (if p = 347 then true else false)) else (if p ≤ 349 then (if p = 349 then true else false) else (if p = 353 then true else false))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then true else false) else (if p = 367 then true else false)) else (if p ≤ 373 then (if p = 373 then true else false) else (if p = 379 then true else false))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then true else false) else (if p ≤ 389 then (if p = 389 then true else false) else (if p = 397 then true else false))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then true else false) else (if p = 409 then true else false)) else (if p ≤ 419 then (if p = 419 then true else false) else (if p = 421 then true else false)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then true else false) else (if p = 433 then true else false)) else (if p ≤ 439 then (if p = 439 then true else false) else (if p = 443 then true else false))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then true else false) else (if p = 457 then true else false)) else (if p ≤ 461 then (if p = 461 then true else false) else (if p = 463 then true else false)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then true else false) else (if p ≤ 479 then (if p = 479 then true else false) else (if p = 487 then true else false))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then true else false) else (if p = 499 then true else false)) else (if p ≤ 503 then (if p = 503 then true else false) else (if p = 509 then true else false)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then true else false) else (if p = 523 then true else false)) else (if p ≤ 541 then (if p = 541 then true else false) else (if p = 547 then true else false))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then true else false) else (if p = 563 then true else false)) else (if p ≤ 569 then (if p = 569 then true else false) else (if p = 571 then true else false))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then true else false) else (if p ≤ 587 then (if p = 587 then true else false) else (if p = 593 then true else false))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then true else false) else (if p = 601 then true else false)) else (if p ≤ 607 then (if p = 607 then true else false) else (if p = 613 then true else false)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then true else false) else (if p = 619 then true else false)) else (if p ≤ 631 then (if p = 631 then true else false) else (if p = 641 then true else false))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then true else false) else (if p = 647 then true else false)) else (if p ≤ 653 then (if p = 653 then true else false) else (if p = 659 then true else false)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then true else false) else (if p ≤ 673 then (if p = 673 then true else false) else (if p = 677 then true else false))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then true else false) else (if p = 691 then true else false)) else (if p ≤ 701 then (if p = 701 then true else false) else (if p = 709 then true else false)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then true else false) else (if p = 727 then true else false)) else (if p ≤ 733 then (if p = 733 then true else false) else (if p = 739 then true else false))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then true else false) else (if p = 751 then true else false)) else (if p ≤ 757 then (if p = 757 then true else false) else (if p = 761 then true else false))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then true else false) else (if p ≤ 773 then (if p = 773 then true else false) else (if p = 787 then true else false))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then true else false) else (if p = 809 then true else false)) else (if p ≤ 811 then (if p = 811 then true else false) else (if p = 821 then true else false)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then true else false) else (if p = 827 then true else false)) else (if p ≤ 829 then (if p = 829 then true else false) else (if p = 839 then true else false))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then true else false) else (if p = 857 then true else false)) else (if p ≤ 859 then (if p = 859 then true else false) else (if p = 863 then true else false)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then true else false) else (if p ≤ 881 then (if p = 881 then true else false) else (if p = 883 then true else false))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then true else false) else (if p = 907 then true else false)) else (if p ≤ 911 then (if p = 911 then true else false) else (if p = 919 then true else false)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then true else false) else (if p = 937 then true else false)) else (if p ≤ 941 then (if p = 941 then true else false) else (if p = 947 then true else false))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then true else false) else (if p = 967 then true else false)) else (if p ≤ 971 then (if p = 971 then true else false) else (if p = 977 then true else false))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then true else false) else (if p ≤ 991 then (if p = 991 then true else false) else (if p = 997 then true else false))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then true else false) else (if p = 1013 then true else false)) else (if p ≤ 1019 then (if p = 1019 then true else false) else (if p = 1021 then true else false)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then true else false) else (if p = 1033 then true else false)) else (if p ≤ 1039 then (if p = 1039 then true else false) else (if p = 1049 then true else false))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then true else false) else (if p = 1061 then true else false)) else (if p ≤ 1063 then (if p = 1063 then true else false) else (if p = 1069 then true else false))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then true else false) else (if p ≤ 1091 then (if p = 1091 then true else false) else (if p = 1093 then true else false))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then true else false) else (if p = 1103 then true else false)) else (if p ≤ 1109 then (if p = 1109 then true else false) else (if p = 1117 then true else false)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then true else false) else (if p = 1129 then true else false)) else (if p ≤ 1151 then (if p = 1151 then true else false) else (if p = 1153 then true else false))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then true else false) else (if p = 1171 then true else false)) else (if p ≤ 1181 then (if p = 1181 then true else false) else (if p = 1187 then true else false))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then true else false) else (if p ≤ 1201 then (if p = 1201 then true else false) else (if p = 1213 then true else false))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then true else false) else (if p = 1223 then true else false)) else (if p ≤ 1229 then (if p = 1229 then true else false) else (if p = 1231 then true else false)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then true else false) else (if p = 1249 then true else false)) else (if p ≤ 1259 then (if p = 1259 then true else false) else (if p = 1277 then true else false))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then true else false) else (if p = 1283 then true else false)) else (if p ≤ 1289 then (if p = 1289 then true else false) else (if p = 1291 then true else false)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then true else false) else (if p ≤ 1301 then (if p = 1301 then true else false) else (if p = 1303 then true else false))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then true else false) else (if p = 1319 then true else false)) else (if p ≤ 1321 then (if p = 1321 then true else false) else (if p = 1327 then true else false)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then true else false) else (if p = 1367 then true else false)) else (if p ≤ 1373 then (if p = 1373 then true else false) else (if p = 1381 then true else false))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then true else false) else (if p = 1409 then true else false)) else (if p ≤ 1423 then (if p = 1423 then true else false) else (if p = 1427 then true else false))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then true else false) else (if p = 1433 then true else false)) else (if p ≤ 1439 then (if p = 1439 then true else false) else (if p = 1447 then true else false))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then true else false) else (if p = 1453 then true else false)) else (if p ≤ 1459 then (if p = 1459 then true else false) else (if p = 1471 then true else false)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then true else false) else (if p = 1483 then true else false)) else (if p ≤ 1487 then (if p = 1487 then true else false) else (if p = 1489 then true else false))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then true else false) else (if p = 1499 then true else false)) else (if p ≤ 1511 then (if p = 1511 then true else false) else (if p = 1523 then true else false))))))))) then (if K = 2 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 559615797935 else 1000000000000) else (if p ≤ 3 then (if p = 3 then 367724790125 else 1000000000000) else (if p = 5 then 215111389616 else 1000000000000))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 151230979723 else 1000000000000) else (if p = 11 then 94558592625 else 1000000000000)) else (if p ≤ 13 then (if p = 13 then 79587447918 else 1000000000000) else (if p = 17 then 60421069474 else 1000000000000)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 53921426793 else 1000000000000) else (if p = 23 then 44369579664 else 1000000000000)) else (if p ≤ 29 then (if p = 29 then 35050326879 else 1000000000000) else (if p = 31 then 32756265074 else 1000000000000))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 27379241825 else 1000000000000) else (if p = 41 then 24678113119 else 1000000000000)) else (if p ≤ 43 then (if p = 43 then 23517929822 else 1000000000000) else (if p = 47 then 21496583397 else 1000000000000))))) else (if K = 3 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 628608669422 else 1000000000000) else (if p ≤ 3 then (if p = 3 then 393042598109 else 1000000000000) else (if p = 5 then 221542279947 else 1000000000000))) else (if p ≤ 7 then (if p = 7 then 153734109942 else 1000000000000) else (if p ≤ 11 then (if p = 11 then 95241886126 else 1000000000000) else (if p = 13 then 80007704280 else 1000000000000)))) else (if K = 4 then (if p ≤ 3 then (if p ≤ 2 then (if p = 2 then 661398492245 else 1000000000000) else (if p = 3 then 401341400924 else 1000000000000)) else (if p ≤ 5 then (if p = 5 then 222823510103 else 1000000000000) else (if p = 7 then 154091189038 else 1000000000000))) else (if K = 5 then (if p ≤ 2 then (if p = 2 then 677398833591 else 1000000000000) else (if p ≤ 3 then (if p = 3 then 404092434296 else 1000000000000) else (if p = 5 then 223079559266 else 1000000000000))) else (if K = 6 then (if p ≤ 2 then (if p = 2 then 685304013098 else 1000000000000) else (if p = 3 then 405007766167 else 1000000000000)) else (if K = 7 then (if p ≤ 2 then (if p = 2 then 689233291238 else 1000000000000) else (if p = 3 then 405312690701 else 1000000000000)) else (if K = 8 then (if p ≤ 2 then (if p = 2 then 691192155724 else 1000000000000) else (if p = 3 then 405414311554 else 1000000000000)) else (if K = 9 then (if p = 2 then 692170150912 else 1000000000000) else (if K = 10 then (if p = 2 then 692658790061 else 1000000000000) else (if K = 11 then (if p = 2 then 692903020127 else 1000000000000) else (if K = 12 then (if p = 2 then 693025112796 else 1000000000000) else 1000000000000)))))))))))
  else 0

def lbNon : ℕ → ℕ := fun p => (if p ≤ 659 then (if p ≤ 281 then (if p ≤ 113 then (if p ≤ 47 then (if p ≤ 17 then (if p ≤ 5 then (if p ≤ 2 then (if p = 2 then 693147170559 else 0) else (if p ≤ 3 then (if p = 3 then 1098612278668 else 0) else (if p = 5 then 1609437902434 else 0))) else (if p ≤ 11 then (if p ≤ 7 then (if p = 7 then 1945910139055 else 0) else (if p = 11 then 2397895262798 else 0)) else (if p ≤ 13 then (if p = 13 then 2564949347461 else 0) else (if p = 17 then 2833213334056 else 0)))) else (if p ≤ 31 then (if p ≤ 23 then (if p ≤ 19 then (if p = 19 then 2944438969166 else 0) else (if p = 23 then 3135494205929 else 0)) else (if p ≤ 29 then (if p = 29 then 3367295819986 else 0) else (if p = 31 then 3433987194485 else 0))) else (if p ≤ 41 then (if p ≤ 37 then (if p = 37 then 3610917902644 else 0) else (if p = 41 then 3713572056704 else 0)) else (if p ≤ 43 then (if p = 43 then 3761200105693 else 0) else (if p = 47 then 3850147591710 else 0))))) else (if p ≤ 79 then (if p ≤ 61 then (if p ≤ 53 then (if p = 53 then 3970291903552 else 0) else (if p ≤ 59 then (if p = 59 then 4077537433905 else 0) else (if p = 61 then 4110873854173 else 0))) else (if p ≤ 71 then (if p ≤ 67 then (if p = 67 then 4204692609390 else 0) else (if p = 71 then 4262679867041 else 0)) else (if p ≤ 73 then (if p = 73 then 4290459431148 else 0) else (if p = 79 then 4369447842467 else 0)))) else (if p ≤ 101 then (if p ≤ 89 then (if p ≤ 83 then (if p = 83 then 4418840597796 else 0) else (if p = 89 then 4488636359732 else 0)) else (if p ≤ 97 then (if p = 97 then 4574710968503 else 0) else (if p = 101 then 4615120506841 else 0))) else (if p ≤ 107 then (if p ≤ 103 then (if p = 103 then 4634728978229 else 0) else (if p = 107 then 4672828824461 else 0)) else (if p ≤ 109 then (if p = 109 then 4691347872229 else 0) else (if p = 113 then 4727387808712 else 0)))))) else (if p ≤ 197 then (if p ≤ 157 then (if p ≤ 137 then (if p ≤ 127 then (if p = 127 then 4844187076458 else 0) else (if p ≤ 131 then (if p = 131 then 4875197313201 else 0) else (if p = 137 then 4919980915828 else 0))) else (if p ≤ 149 then (if p ≤ 139 then (if p = 139 then 4934473923130 else 0) else (if p = 149 then 5003946295945 else 0)) else (if p ≤ 151 then (if p = 151 then 5017279826814 else 0) else (if p = 157 then 5056245795348 else 0)))) else (if p ≤ 179 then (if p ≤ 167 then (if p ≤ 163 then (if p = 163 then 5093750190806 else 0) else (if p = 167 then 5117993802416 else 0)) else (if p ≤ 173 then (if p = 173 then 5153291584497 else 0) else (if p = 179 then 5187385795840 else 0))) else (if p ≤ 191 then (if p ≤ 181 then (if p = 181 then 5198497021265 else 0) else (if p = 191 then 5252273418046 else 0)) else (if p ≤ 193 then (if p = 193 then 5262690178904 else 0) else (if p = 197 then 5283203718737 else 0))))) else (if p ≤ 239 then (if p ≤ 223 then (if p ≤ 199 then (if p = 199 then 5293304814724 else 0) else (if p ≤ 211 then (if p = 211 then 5351858123476 else 0) else (if p = 223 then 5407171761460 else 0))) else (if p ≤ 229 then (if p ≤ 227 then (if p = 227 then 5424950007481 else 0) else (if p = 229 then 5433721993554 else 0)) else (if p ≤ 233 then (if p = 233 then 5451038443565 else 0) else (if p = 239 then 5476463541931 else 0)))) else (if p ≤ 263 then (if p ≤ 251 then (if p ≤ 241 then (if p = 241 then 5484796923490 else 0) else (if p = 251 then 5525452929131 else 0)) else (if p ≤ 257 then (if p = 257 then 5549076074895 else 0) else (if p = 263 then 5572154022177 else 0))) else (if p ≤ 271 then (if p ≤ 269 then (if p = 269 then 5594711369601 else 0) else (if p = 271 then 5602118810879 else 0)) else (if p ≤ 277 then (if p = 277 then 5624017496187 else 0) else (if p = 281 then 5638354659333 else 0))))))) else (if p ≤ 463 then (if p ≤ 379 then (if p ≤ 331 then (if p ≤ 307 then (if p ≤ 283 then (if p = 283 then 5645446887643 else 0) else (if p ≤ 293 then (if p = 293 then 5680172599017 else 0) else (if p = 307 then 5726847737587 else 0))) else (if p ≤ 313 then (if p ≤ 311 then (if p = 311 then 5739792902179 else 0) else (if p = 313 then 5746203180540 else 0)) else (if p ≤ 317 then (if p = 317 then 5758901763877 else 0) else (if p = 331 then 5802118365377 else 0)))) else (if p ≤ 353 then (if p ≤ 347 then (if p ≤ 337 then (if p = 337 then 5820082920352 else 0) else (if p = 347 then 5849324769946 else 0)) else (if p ≤ 349 then (if p = 349 then 5855071912202 else 0) else (if p = 353 then 5866468046933 else 0))) else (if p ≤ 367 then (if p ≤ 359 then (if p = 359 then 5883322378488 else 0) else (if p = 367 then 5905361838054 else 0)) else (if p ≤ 373 then (if p = 373 then 5921578409643 else 0) else (if p = 379 then 5937536195082 else 0))))) else (if p ≤ 421 then (if p ≤ 397 then (if p ≤ 383 then (if p = 383 then 5948034979180 else 0) else (if p ≤ 389 then (if p = 389 then 5963579333618 else 0) else (if p = 397 then 5983936270687 else 0))) else (if p ≤ 409 then (if p ≤ 401 then (if p = 401 then 5993961417306 else 0) else (if p = 409 then 6013715146042 else 0)) else (if p ≤ 419 then (if p = 419 then 6037870909922 else 0) else (if p = 421 then 6042632823682 else 0)))) else (if p ≤ 443 then (if p ≤ 433 then (if p ≤ 431 then (if p = 431 then 6066108080103 else 0) else (if p = 433 then 6070737718002 else 0)) else (if p ≤ 439 then (if p = 439 then 6084499403075 else 0) else (if p = 443 then 6093569760045 else 0))) else (if p ≤ 457 then (if p ≤ 449 then (if p = 449 then 6107022877742 else 0) else (if p = 457 then 6124683380894 else 0)) else (if p ≤ 461 then (if p = 461 then 6133398032996 else 0) else (if p = 463 then 6137727044086 else 0)))))) else (if p ≤ 571 then (if p ≤ 509 then (if p ≤ 487 then (if p ≤ 467 then (if p = 467 then 6146329247668 else 0) else (if p ≤ 479 then (if p = 479 then 6171700587410 else 0) else (if p = 487 then 6188264113082 else 0))) else (if p ≤ 499 then (if p ≤ 491 then (if p = 491 then 6196444117794 else 0) else (if p = 499 then 6212606085751 else 0)) else (if p ≤ 503 then (if p = 503 then 6220590160099 else 0) else (if p = 509 then 6232448006550 else 0)))) else (if p ≤ 547 then (if p ≤ 523 then (if p ≤ 521 then (if p = 521 then 6255750031753 else 0) else (if p = 523 then 6259581454064 else 0)) else (if p ≤ 541 then (if p = 541 then 6293419268846 else 0) else (if p = 547 then 6304448792421 else 0))) else (if p ≤ 563 then (if p ≤ 557 then (if p = 557 then 6322565229927 else 0) else (if p = 563 then 6333279618139 else 0)) else (if p ≤ 569 then (if p = 569 then 6343880424126 else 0) else (if p = 571 then 6347389199656 else 0))))) else (if p ≤ 613 then (if p ≤ 593 then (if p ≤ 577 then (if p = 577 then 6357842256508 else 0) else (if p ≤ 587 then (if p = 587 then 6375024809828 else 0) else (if p = 593 then 6385194388997 else 0))) else (if p ≤ 601 then (if p ≤ 599 then (if p = 599 then 6395261588115 else 0) else (if p = 601 then 6398594924535 else 0)) else (if p ≤ 607 then (if p = 607 then 6408528781059 else 0) else (if p = 613 then 6418364925936 else 0)))) else (if p ≤ 641 then (if p ≤ 619 then (if p ≤ 617 then (if p = 617 then 6424869013905 else 0) else (if p = 619 then 6428105262684 else 0)) else (if p ≤ 631 then (if p = 631 then 6447305852541 else 0) else (if p = 641 then 6463029446920 else 0))) else (if p ≤ 647 then (if p ≤ 643 then (if p = 643 then 6466144714237 else 0) else (if p = 647 then 6472346284500 else 0)) else (if p ≤ 653 then (if p = 653 then 6481577119276 else 0) else (if p = 659 then 6490723524502 else 0)))))))) else (if p ≤ 1069 then (if p ≤ 863 then (if p ≤ 761 then (if p ≤ 709 then (if p ≤ 677 then (if p ≤ 661 then (if p = 661 then 6493753829851 else 0) else (if p ≤ 673 then (if p = 673 then 6511745319644 else 0) else (if p = 677 then 6517671262912 else 0))) else (if p ≤ 691 then (if p ≤ 683 then (if p = 683 then 6526494849570 else 0) else (if p = 691 then 6538139813767 else 0)) else (if p ≤ 701 then (if p = 701 then 6552507877034 else 0) else (if p = 709 then 6563855516532 else 0)))) else (if p ≤ 739 then (if p ≤ 727 then (if p ≤ 719 then (if p = 719 then 6577861347721 else 0) else (if p = 727 then 6588926467533 else 0)) else (if p ≤ 733 then (if p = 733 then 6597145691886 else 0) else (if p = 739 then 6605297910948 else 0))) else (if p ≤ 751 then (if p ≤ 743 then (if p = 743 then 6610696034717 else 0) else (if p = 751 then 6621405641764 else 0)) else (if p ≤ 757 then (if p = 757 then 6629363243437 else 0) else (if p = 761 then 6634633347861 else 0))))) else (if p ≤ 821 then (if p ≤ 787 then (if p ≤ 769 then (if p = 769 then 6645090959505 else 0) else (if p ≤ 773 then (if p = 773 then 6650279038587 else 0) else (if p = 787 then 6668228238417 else 0))) else (if p ≤ 809 then (if p ≤ 797 then (if p = 797 then 6680854668790 else 0) else (if p = 809 then 6695798907058 else 0)) else (if p ≤ 811 then (if p = 811 then 6698268044115 else 0) else (if p = 821 then 6710523099452 else 0)))) else (if p ≤ 839 then (if p ≤ 827 then (if p ≤ 823 then (if p = 823 then 6712956190677 else 0) else (if p = 827 then 6717804685023 else 0)) else (if p ≤ 829 then (if p = 829 then 6720220145135 else 0) else (if p = 839 then 6732210696467 else 0))) else (if p ≤ 857 then (if p ≤ 853 then (if p = 853 then 6748759537491 else 0) else (if p = 857 then 6753437908597 else 0)) else (if p ≤ 859 then (if p = 859 then 6755768911984 else 0) else (if p = 863 then 6760414681083 else 0)))))) else (if p ≤ 977 then (if p ≤ 919 then (if p ≤ 883 then (if p ≤ 877 then (if p = 877 then 6776506982372 else 0) else (if p ≤ 881 then (if p = 881 then 6781057615936 else 0) else (if p = 883 then 6783325190603 else 0))) else (if p ≤ 907 then (if p ≤ 887 then (if p = 887 then 6787844972309 else 0) else (if p = 907 then 6810142440115 else 0)) else (if p ≤ 911 then (if p = 911 then 6814542887259 else 0) else (if p = 919 then 6823286112355 else 0)))) else (if p ≤ 947 then (if p ≤ 937 then (if p ≤ 929 then (if p = 929 then 6834108728813 else 0) else (if p = 937 then 6842683272238 else 0)) else (if p ≤ 941 then (if p = 941 then 6846943129585 else 0) else (if p = 947 then 6853299083186 else 0))) else (if p ≤ 967 then (if p ≤ 953 then (if p = 953 then 6859614893654 else 0) else (if p = 967 then 6874198485453 else 0)) else (if p ≤ 971 then (if p = 971 then 6878326458291 else 0) else (if p = 977 then 6884486642042 else 0))))) else (if p ≤ 1021 then (if p ≤ 997 then (if p ≤ 983 then (if p = 983 then 6890609110147 else 0) else (if p ≤ 991 then (if p = 991 then 6898714524329 else 0) else (if p = 997 then 6904750759961 else 0))) else (if p ≤ 1013 then (if p ≤ 1009 then (if p = 1009 then 6916715010353 else 0) else (if p = 1013 then 6920671494248 else 0)) else (if p ≤ 1019 then (if p = 1019 then 6926577023222 else 0) else (if p = 1021 then 6928537808164 else 0)))) else (if p ≤ 1049 then (if p ≤ 1033 then (if p ≤ 1031 then (if p = 1031 then 6938284474016 else 0) else (if p = 1033 then 6940222459119 else 0)) else (if p ≤ 1039 then (if p = 1039 then 6946013981099 else 0) else (if p = 1049 then 6955592598396 else 0))) else (if p ≤ 1061 then (if p ≤ 1051 then (if p = 1051 then 6957497360876 else 0) else (if p = 1061 then 6966967128613 else 0)) else (if p ≤ 1063 then (if p = 1063 then 6968850368341 else 0) else (if p = 1069 then 6974478901025 else 0))))))) else (if p ≤ 1291 then (if p ≤ 1187 then (if p ≤ 1117 then (if p ≤ 1093 then (if p ≤ 1087 then (if p = 1087 then 6991176877121 else 0) else (if p ≤ 1091 then (if p = 1091 then 6994849975833 else 0) else (if p = 1093 then 6996681478176 else 0))) else (if p ≤ 1103 then (if p ≤ 1097 then (if p = 1097 then 7000334450275 else 0) else (if p = 1103 then 7005789009253 else 0)) else (if p ≤ 1109 then (if p = 1109 then 7011213977350 else 0) else (if p = 1117 then 7018401789069 else 0)))) else (if p ≤ 1153 then (if p ≤ 1129 then (if p ≤ 1123 then (if p = 1123 then 7023758944738 else 0) else (if p = 1129 then 7029087554149 else 0)) else (if p ≤ 1151 then (if p = 1151 then 7048386398721 else 0) else (if p = 1153 then 7050122510269 else 0))) else (if p ≤ 1171 then (if p ≤ 1163 then (if p = 1163 then 7058758142518 else 0) else (if p = 1171 then 7065613353597 else 0)) else (if p ≤ 1181 then (if p = 1181 then 7074116806197 else 0) else (if p = 1187 then 7079184384609 else 0))))) else (if p ≤ 1231 then (if p ≤ 1213 then (if p ≤ 1193 then (if p = 1193 then 7084226412097 else 0) else (if p ≤ 1201 then (if p = 1201 then 7090909812079 else 0) else (if p = 1213 then 7100851898944 else 0))) else (if p ≤ 1223 then (if p ≤ 1217 then (if p = 1217 then 7104144082987 else 0) else (if p = 1223 then 7109062125687 else 0)) else (if p ≤ 1229 then (if p = 1229 then 7113956099566 else 0) else (if p = 1231 then 7115582116184 else 0)))) else (if p ≤ 1277 then (if p ≤ 1249 then (if p ≤ 1237 then (if p = 1237 then 7120444362392 else 0) else (if p = 1249 then 7130098500125 else 0)) else (if p ≤ 1259 then (if p = 1259 then 7138073024044 else 0) else (if p = 1277 then 7152268846032 else 0))) else (if p ≤ 1283 then (if p ≤ 1279 then (if p = 1279 then 7153833791578 else 0) else (if p = 1283 then 7156956354615 else 0)) else (if p ≤ 1289 then (if p = 1289 then 7161621992939 else 0) else (if p = 1291 then 7163172380846 else 0)))))) else (if p ≤ 1427 then (if p ≤ 1327 then (if p ≤ 1303 then (if p ≤ 1297 then (if p = 1297 then 7167809174316 else 0) else (if p ≤ 1301 then (if p = 1301 then 7170888468512 else 0) else (if p = 1303 then 7172424567124 else 0))) else (if p ≤ 1319 then (if p ≤ 1307 then (if p = 1307 then 7175489703624 else 0) else (if p = 1319 then 7184629142717 else 0)) else (if p ≤ 1321 then (if p = 1321 then 7186144294522 else 0) else (if p = 1327 then 7190676024332 else 0)))) else (if p ≤ 1381 then (if p ≤ 1367 then (if p ≤ 1361 then (if p = 1361 then 7215974992651 else 0) else (if p = 1367 then 7220373826723 else 0)) else (if p ≤ 1373 then (if p = 1373 then 7224753395767 else 0) else (if p = 1381 then 7230563143409 else 0))) else (if p ≤ 1409 then (if p ≤ 1399 then (if p = 1399 then 7243512964665 else 0) else (if p = 1409 then 7250635501898 else 0)) else (if p ≤ 1423 then (if p = 1423 then 7260522588089 else 0) else (if p = 1427 then 7263329607476 else 0))))) else (if p ≤ 1471 then (if p ≤ 1447 then (if p ≤ 1433 then (if p ≤ 1429 then (if p = 1429 then 7264730167929 else 0) else (if p = 1433 then 7267525417828 else 0)) else (if p ≤ 1439 then (if p = 1439 then 7271703696887 else 0) else (if p = 1447 then 7277247716631 else 0))) else (if p ≤ 1453 then (if p ≤ 1451 then (if p = 1451 then 7280008242884 else 0) else (if p = 1453 then 7281385653570 else 0)) else (if p ≤ 1459 then (if p = 1459 then 7285506538522 else 0) else (if p = 1471 then 7293697710601 else 0)))) else (if p ≤ 1489 then (if p ≤ 1483 then (if p ≤ 1481 then (if p = 1481 then 7300472804267 else 0) else (if p = 1483 then 7301822332137 else 0)) else (if p ≤ 1487 then (if p = 1487 then 7304515936460 else 0) else (if p = 1489 then 7305860022684 else 0))) else (if p ≤ 1499 then (if p ≤ 1493 then (if p = 1493 then 7308542787539 else 0) else (if p = 1499 then 7312553488102 else 0)) else (if p ≤ 1511 then (if p = 1511 then 7320526952272 else 0) else (if p = 1523 then 7328437342895 else 0)))))))))

def blkIdx : ℕ → ℕ := fun xi => (if xi ≤ 659 then (if xi ≤ 281 then (if xi ≤ 113 then (if xi ≤ 47 then (if xi ≤ 17 then (if xi ≤ 5 then (if xi ≤ 2 then (if xi = 2 then 0 else 0) else (if xi ≤ 3 then (if xi = 3 then 0 else 0) else (if xi = 5 then 0 else 0))) else (if xi ≤ 11 then (if xi ≤ 7 then (if xi = 7 then 0 else 0) else (if xi = 11 then 0 else 0)) else (if xi ≤ 13 then (if xi = 13 then 0 else 0) else (if xi = 17 then 0 else 0)))) else (if xi ≤ 31 then (if xi ≤ 23 then (if xi ≤ 19 then (if xi = 19 then 1 else 0) else (if xi = 23 then 2 else 0)) else (if xi ≤ 29 then (if xi = 29 then 3 else 0) else (if xi = 31 then 4 else 0))) else (if xi ≤ 41 then (if xi ≤ 37 then (if xi = 37 then 5 else 0) else (if xi = 41 then 5 else 0)) else (if xi ≤ 43 then (if xi = 43 then 6 else 0) else (if xi = 47 then 7 else 0))))) else (if xi ≤ 79 then (if xi ≤ 61 then (if xi ≤ 53 then (if xi = 53 then 7 else 0) else (if xi ≤ 59 then (if xi = 59 then 8 else 0) else (if xi = 61 then 9 else 0))) else (if xi ≤ 71 then (if xi ≤ 67 then (if xi = 67 then 9 else 0) else (if xi = 71 then 10 else 0)) else (if xi ≤ 73 then (if xi = 73 then 11 else 0) else (if xi = 79 then 12 else 0)))) else (if xi ≤ 101 then (if xi ≤ 89 then (if xi ≤ 83 then (if xi = 83 then 12 else 0) else (if xi = 89 then 13 else 0)) else (if xi ≤ 97 then (if xi = 97 then 13 else 0) else (if xi = 101 then 14 else 0))) else (if xi ≤ 107 then (if xi ≤ 103 then (if xi = 103 then 14 else 0) else (if xi = 107 then 15 else 0)) else (if xi ≤ 109 then (if xi = 109 then 15 else 0) else (if xi = 113 then 16 else 0)))))) else (if xi ≤ 197 then (if xi ≤ 157 then (if xi ≤ 137 then (if xi ≤ 127 then (if xi = 127 then 16 else 0) else (if xi ≤ 131 then (if xi = 131 then 17 else 0) else (if xi = 137 then 17 else 0))) else (if xi ≤ 149 then (if xi ≤ 139 then (if xi = 139 then 18 else 0) else (if xi = 149 then 18 else 0)) else (if xi ≤ 151 then (if xi = 151 then 19 else 0) else (if xi = 157 then 19 else 0)))) else (if xi ≤ 179 then (if xi ≤ 167 then (if xi ≤ 163 then (if xi = 163 then 20 else 0) else (if xi = 167 then 20 else 0)) else (if xi ≤ 173 then (if xi = 173 then 21 else 0) else (if xi = 179 then 21 else 0))) else (if xi ≤ 191 then (if xi ≤ 181 then (if xi = 181 then 21 else 0) else (if xi = 191 then 22 else 0)) else (if xi ≤ 193 then (if xi = 193 then 22 else 0) else (if xi = 197 then 22 else 0))))) else (if xi ≤ 239 then (if xi ≤ 223 then (if xi ≤ 199 then (if xi = 199 then 23 else 0) else (if xi ≤ 211 then (if xi = 211 then 23 else 0) else (if xi = 223 then 24 else 0))) else (if xi ≤ 229 then (if xi ≤ 227 then (if xi = 227 then 24 else 0) else (if xi = 229 then 25 else 0)) else (if xi ≤ 233 then (if xi = 233 then 25 else 0) else (if xi = 239 then 26 else 0)))) else (if xi ≤ 263 then (if xi ≤ 251 then (if xi ≤ 241 then (if xi = 241 then 26 else 0) else (if xi = 251 then 26 else 0)) else (if xi ≤ 257 then (if xi = 257 then 27 else 0) else (if xi = 263 then 27 else 0))) else (if xi ≤ 271 then (if xi ≤ 269 then (if xi = 269 then 27 else 0) else (if xi = 271 then 28 else 0)) else (if xi ≤ 277 then (if xi = 277 then 28 else 0) else (if xi = 281 then 28 else 0))))))) else (if xi ≤ 463 then (if xi ≤ 379 then (if xi ≤ 331 then (if xi ≤ 307 then (if xi ≤ 283 then (if xi = 283 then 29 else 0) else (if xi ≤ 293 then (if xi = 293 then 29 else 0) else (if xi = 307 then 30 else 0))) else (if xi ≤ 313 then (if xi ≤ 311 then (if xi = 311 then 30 else 0) else (if xi = 313 then 30 else 0)) else (if xi ≤ 317 then (if xi = 317 then 31 else 0) else (if xi = 331 then 31 else 0)))) else (if xi ≤ 353 then (if xi ≤ 347 then (if xi ≤ 337 then (if xi = 337 then 31 else 0) else (if xi = 347 then 32 else 0)) else (if xi ≤ 349 then (if xi = 349 then 32 else 0) else (if xi = 353 then 32 else 0))) else (if xi ≤ 367 then (if xi ≤ 359 then (if xi = 359 then 33 else 0) else (if xi = 367 then 33 else 0)) else (if xi ≤ 373 then (if xi = 373 then 33 else 0) else (if xi = 379 then 34 else 0))))) else (if xi ≤ 421 then (if xi ≤ 397 then (if xi ≤ 383 then (if xi = 383 then 34 else 0) else (if xi ≤ 389 then (if xi = 389 then 34 else 0) else (if xi = 397 then 35 else 0))) else (if xi ≤ 409 then (if xi ≤ 401 then (if xi = 401 then 35 else 0) else (if xi = 409 then 35 else 0)) else (if xi ≤ 419 then (if xi = 419 then 36 else 0) else (if xi = 421 then 36 else 0)))) else (if xi ≤ 443 then (if xi ≤ 433 then (if xi ≤ 431 then (if xi = 431 then 36 else 0) else (if xi = 433 then 37 else 0)) else (if xi ≤ 439 then (if xi = 439 then 37 else 0) else (if xi = 443 then 37 else 0))) else (if xi ≤ 457 then (if xi ≤ 449 then (if xi = 449 then 38 else 0) else (if xi = 457 then 38 else 0)) else (if xi ≤ 461 then (if xi = 461 then 38 else 0) else (if xi = 463 then 39 else 0)))))) else (if xi ≤ 571 then (if xi ≤ 509 then (if xi ≤ 487 then (if xi ≤ 467 then (if xi = 467 then 39 else 0) else (if xi ≤ 479 then (if xi = 479 then 39 else 0) else (if xi = 487 then 40 else 0))) else (if xi ≤ 499 then (if xi ≤ 491 then (if xi = 491 then 40 else 0) else (if xi = 499 then 40 else 0)) else (if xi ≤ 503 then (if xi = 503 then 41 else 0) else (if xi = 509 then 41 else 0)))) else (if xi ≤ 547 then (if xi ≤ 523 then (if xi ≤ 521 then (if xi = 521 then 41 else 0) else (if xi = 523 then 42 else 0)) else (if xi ≤ 541 then (if xi = 541 then 42 else 0) else (if xi = 547 then 43 else 0))) else (if xi ≤ 563 then (if xi ≤ 557 then (if xi = 557 then 43 else 0) else (if xi = 563 then 43 else 0)) else (if xi ≤ 569 then (if xi = 569 then 44 else 0) else (if xi = 571 then 44 else 0))))) else (if xi ≤ 613 then (if xi ≤ 593 then (if xi ≤ 577 then (if xi = 577 then 44 else 0) else (if xi ≤ 587 then (if xi = 587 then 44 else 0) else (if xi = 593 then 45 else 0))) else (if xi ≤ 601 then (if xi ≤ 599 then (if xi = 599 then 45 else 0) else (if xi = 601 then 45 else 0)) else (if xi ≤ 607 then (if xi = 607 then 45 else 0) else (if xi = 613 then 46 else 0)))) else (if xi ≤ 641 then (if xi ≤ 619 then (if xi ≤ 617 then (if xi = 617 then 46 else 0) else (if xi = 619 then 46 else 0)) else (if xi ≤ 631 then (if xi = 631 then 46 else 0) else (if xi = 641 then 47 else 0))) else (if xi ≤ 647 then (if xi ≤ 643 then (if xi = 643 then 47 else 0) else (if xi = 647 then 47 else 0)) else (if xi ≤ 653 then (if xi = 653 then 47 else 0) else (if xi = 659 then 48 else 0)))))))) else (if xi ≤ 1069 then (if xi ≤ 863 then (if xi ≤ 761 then (if xi ≤ 709 then (if xi ≤ 677 then (if xi ≤ 661 then (if xi = 661 then 48 else 0) else (if xi ≤ 673 then (if xi = 673 then 48 else 0) else (if xi = 677 then 48 else 0))) else (if xi ≤ 691 then (if xi ≤ 683 then (if xi = 683 then 49 else 0) else (if xi = 691 then 49 else 0)) else (if xi ≤ 701 then (if xi = 701 then 49 else 0) else (if xi = 709 then 49 else 0)))) else (if xi ≤ 739 then (if xi ≤ 727 then (if xi ≤ 719 then (if xi = 719 then 50 else 0) else (if xi = 727 then 50 else 0)) else (if xi ≤ 733 then (if xi = 733 then 50 else 0) else (if xi = 739 then 50 else 0))) else (if xi ≤ 751 then (if xi ≤ 743 then (if xi = 743 then 51 else 0) else (if xi = 751 then 51 else 0)) else (if xi ≤ 757 then (if xi = 757 then 51 else 0) else (if xi = 761 then 52 else 0))))) else (if xi ≤ 821 then (if xi ≤ 787 then (if xi ≤ 769 then (if xi = 769 then 52 else 0) else (if xi ≤ 773 then (if xi = 773 then 52 else 0) else (if xi = 787 then 53 else 0))) else (if xi ≤ 809 then (if xi ≤ 797 then (if xi = 797 then 53 else 0) else (if xi = 809 then 53 else 0)) else (if xi ≤ 811 then (if xi = 811 then 53 else 0) else (if xi = 821 then 54 else 0)))) else (if xi ≤ 839 then (if xi ≤ 827 then (if xi ≤ 823 then (if xi = 823 then 54 else 0) else (if xi = 827 then 54 else 0)) else (if xi ≤ 829 then (if xi = 829 then 54 else 0) else (if xi = 839 then 55 else 0))) else (if xi ≤ 857 then (if xi ≤ 853 then (if xi = 853 then 55 else 0) else (if xi = 857 then 55 else 0)) else (if xi ≤ 859 then (if xi = 859 then 55 else 0) else (if xi = 863 then 56 else 0)))))) else (if xi ≤ 977 then (if xi ≤ 919 then (if xi ≤ 883 then (if xi ≤ 877 then (if xi = 877 then 56 else 0) else (if xi ≤ 881 then (if xi = 881 then 56 else 0) else (if xi = 883 then 56 else 0))) else (if xi ≤ 907 then (if xi ≤ 887 then (if xi = 887 then 57 else 0) else (if xi = 907 then 57 else 0)) else (if xi ≤ 911 then (if xi = 911 then 57 else 0) else (if xi = 919 then 58 else 0)))) else (if xi ≤ 947 then (if xi ≤ 937 then (if xi ≤ 929 then (if xi = 929 then 58 else 0) else (if xi = 937 then 58 else 0)) else (if xi ≤ 941 then (if xi = 941 then 59 else 0) else (if xi = 947 then 59 else 0))) else (if xi ≤ 967 then (if xi ≤ 953 then (if xi = 953 then 59 else 0) else (if xi = 967 then 59 else 0)) else (if xi ≤ 971 then (if xi = 971 then 60 else 0) else (if xi = 977 then 60 else 0))))) else (if xi ≤ 1021 then (if xi ≤ 997 then (if xi ≤ 983 then (if xi = 983 then 60 else 0) else (if xi ≤ 991 then (if xi = 991 then 60 else 0) else (if xi = 997 then 61 else 0))) else (if xi ≤ 1013 then (if xi ≤ 1009 then (if xi = 1009 then 61 else 0) else (if xi = 1013 then 61 else 0)) else (if xi ≤ 1019 then (if xi = 1019 then 61 else 0) else (if xi = 1021 then 62 else 0)))) else (if xi ≤ 1049 then (if xi ≤ 1033 then (if xi ≤ 1031 then (if xi = 1031 then 62 else 0) else (if xi = 1033 then 62 else 0)) else (if xi ≤ 1039 then (if xi = 1039 then 62 else 0) else (if xi = 1049 then 63 else 0))) else (if xi ≤ 1061 then (if xi ≤ 1051 then (if xi = 1051 then 63 else 0) else (if xi = 1061 then 63 else 0)) else (if xi ≤ 1063 then (if xi = 1063 then 63 else 0) else (if xi = 1069 then 64 else 0))))))) else (if xi ≤ 1291 then (if xi ≤ 1187 then (if xi ≤ 1117 then (if xi ≤ 1093 then (if xi ≤ 1087 then (if xi = 1087 then 64 else 0) else (if xi ≤ 1091 then (if xi = 1091 then 64 else 0) else (if xi = 1093 then 64 else 0))) else (if xi ≤ 1103 then (if xi ≤ 1097 then (if xi = 1097 then 65 else 0) else (if xi = 1103 then 65 else 0)) else (if xi ≤ 1109 then (if xi = 1109 then 65 else 0) else (if xi = 1117 then 65 else 0)))) else (if xi ≤ 1153 then (if xi ≤ 1129 then (if xi ≤ 1123 then (if xi = 1123 then 66 else 0) else (if xi = 1129 then 66 else 0)) else (if xi ≤ 1151 then (if xi = 1151 then 66 else 0) else (if xi = 1153 then 66 else 0))) else (if xi ≤ 1171 then (if xi ≤ 1163 then (if xi = 1163 then 67 else 0) else (if xi = 1171 then 67 else 0)) else (if xi ≤ 1181 then (if xi = 1181 then 67 else 0) else (if xi = 1187 then 67 else 0))))) else (if xi ≤ 1231 then (if xi ≤ 1213 then (if xi ≤ 1193 then (if xi = 1193 then 68 else 0) else (if xi ≤ 1201 then (if xi = 1201 then 68 else 0) else (if xi = 1213 then 68 else 0))) else (if xi ≤ 1223 then (if xi ≤ 1217 then (if xi = 1217 then 68 else 0) else (if xi = 1223 then 69 else 0)) else (if xi ≤ 1229 then (if xi = 1229 then 69 else 0) else (if xi = 1231 then 69 else 0)))) else (if xi ≤ 1277 then (if xi ≤ 1249 then (if xi ≤ 1237 then (if xi = 1237 then 69 else 0) else (if xi = 1249 then 70 else 0)) else (if xi ≤ 1259 then (if xi = 1259 then 70 else 0) else (if xi = 1277 then 70 else 0))) else (if xi ≤ 1283 then (if xi ≤ 1279 then (if xi = 1279 then 70 else 0) else (if xi = 1283 then 71 else 0)) else (if xi ≤ 1289 then (if xi = 1289 then 71 else 0) else (if xi = 1291 then 71 else 0)))))) else (if xi ≤ 1427 then (if xi ≤ 1327 then (if xi ≤ 1303 then (if xi ≤ 1297 then (if xi = 1297 then 71 else 0) else (if xi ≤ 1301 then (if xi = 1301 then 72 else 0) else (if xi = 1303 then 72 else 0))) else (if xi ≤ 1319 then (if xi ≤ 1307 then (if xi = 1307 then 72 else 0) else (if xi = 1319 then 72 else 0)) else (if xi ≤ 1321 then (if xi = 1321 then 73 else 0) else (if xi = 1327 then 73 else 0)))) else (if xi ≤ 1381 then (if xi ≤ 1367 then (if xi ≤ 1361 then (if xi = 1361 then 73 else 0) else (if xi = 1367 then 73 else 0)) else (if xi ≤ 1373 then (if xi = 1373 then 74 else 0) else (if xi = 1381 then 74 else 0))) else (if xi ≤ 1409 then (if xi ≤ 1399 then (if xi = 1399 then 74 else 0) else (if xi = 1409 then 74 else 0)) else (if xi ≤ 1423 then (if xi = 1423 then 75 else 0) else (if xi = 1427 then 75 else 0))))) else (if xi ≤ 1471 then (if xi ≤ 1447 then (if xi ≤ 1433 then (if xi ≤ 1429 then (if xi = 1429 then 75 else 0) else (if xi = 1433 then 75 else 0)) else (if xi ≤ 1439 then (if xi = 1439 then 76 else 0) else (if xi = 1447 then 76 else 0))) else (if xi ≤ 1453 then (if xi ≤ 1451 then (if xi = 1451 then 76 else 0) else (if xi = 1453 then 76 else 0)) else (if xi ≤ 1459 then (if xi = 1459 then 77 else 0) else (if xi = 1471 then 77 else 0)))) else (if xi ≤ 1489 then (if xi ≤ 1483 then (if xi ≤ 1481 then (if xi = 1481 then 77 else 0) else (if xi = 1483 then 77 else 0)) else (if xi ≤ 1487 then (if xi = 1487 then 78 else 0) else (if xi = 1489 then 78 else 0))) else (if xi ≤ 1499 then (if xi ≤ 1493 then (if xi = 1493 then 78 else 0) else (if xi = 1499 then 78 else 0)) else (if xi ≤ 1511 then (if xi = 1511 then 79 else 0) else (if xi = 1523 then 79 else 0)))))))))

def blkA : ℕ → ℕ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 17 else 0) else (if i = 1 then 19 else 0)) else (if i ≤ 2 then (if i = 2 then 23 else 0) else (if i ≤ 3 then (if i = 3 then 29 else 0) else (if i = 4 then 31 else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 37 else 0) else (if i = 6 then 43 else 0)) else (if i ≤ 7 then (if i = 7 then 47 else 0) else (if i ≤ 8 then (if i = 8 then 59 else 0) else (if i = 9 then 61 else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 71 else 0) else (if i = 11 then 73 else 0)) else (if i ≤ 12 then (if i = 12 then 79 else 0) else (if i ≤ 13 then (if i = 13 then 89 else 0) else (if i = 14 then 101 else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 107 else 0) else (if i = 16 then 113 else 0)) else (if i ≤ 17 then (if i = 17 then 131 else 0) else (if i ≤ 18 then (if i = 18 then 139 else 0) else (if i = 19 then 151 else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 163 else 0) else (if i = 21 then 173 else 0)) else (if i ≤ 22 then (if i = 22 then 191 else 0) else (if i ≤ 23 then (if i = 23 then 199 else 0) else (if i = 24 then 223 else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 229 else 0) else (if i = 26 then 239 else 0)) else (if i ≤ 27 then (if i = 27 then 257 else 0) else (if i ≤ 28 then (if i = 28 then 271 else 0) else (if i = 29 then 283 else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 307 else 0) else (if i = 31 then 317 else 0)) else (if i ≤ 32 then (if i = 32 then 347 else 0) else (if i ≤ 33 then (if i = 33 then 359 else 0) else (if i = 34 then 379 else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 397 else 0) else (if i = 36 then 419 else 0)) else (if i ≤ 37 then (if i = 37 then 433 else 0) else (if i ≤ 38 then (if i = 38 then 449 else 0) else (if i = 39 then 463 else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 487 else 0) else (if i = 41 then 503 else 0)) else (if i ≤ 42 then (if i = 42 then 523 else 0) else (if i ≤ 43 then (if i = 43 then 547 else 0) else (if i = 44 then 569 else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 593 else 0) else (if i = 46 then 613 else 0)) else (if i ≤ 47 then (if i = 47 then 641 else 0) else (if i ≤ 48 then (if i = 48 then 659 else 0) else (if i = 49 then 683 else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 719 else 0) else (if i = 51 then 743 else 0)) else (if i ≤ 52 then (if i = 52 then 761 else 0) else (if i ≤ 53 then (if i = 53 then 787 else 0) else (if i = 54 then 821 else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 839 else 0) else (if i = 56 then 863 else 0)) else (if i ≤ 57 then (if i = 57 then 887 else 0) else (if i ≤ 58 then (if i = 58 then 919 else 0) else (if i = 59 then 941 else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 971 else 0) else (if i = 61 then 997 else 0)) else (if i ≤ 62 then (if i = 62 then 1021 else 0) else (if i ≤ 63 then (if i = 63 then 1049 else 0) else (if i = 64 then 1069 else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1097 else 0) else (if i = 66 then 1123 else 0)) else (if i ≤ 67 then (if i = 67 then 1163 else 0) else (if i ≤ 68 then (if i = 68 then 1193 else 0) else (if i = 69 then 1223 else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 1249 else 0) else (if i = 71 then 1283 else 0)) else (if i ≤ 72 then (if i = 72 then 1301 else 0) else (if i ≤ 73 then (if i = 73 then 1321 else 0) else (if i = 74 then 1373 else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 1423 else 0) else (if i = 76 then 1439 else 0)) else (if i ≤ 77 then (if i = 77 then 1459 else 0) else (if i ≤ 78 then (if i = 78 then 1487 else 0) else (if i = 79 then 1511 else 0))))))))

def blkB : ℕ → ℕ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 17 else 0) else (if i = 1 then 19 else 0)) else (if i ≤ 2 then (if i = 2 then 23 else 0) else (if i ≤ 3 then (if i = 3 then 29 else 0) else (if i = 4 then 31 else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 41 else 0) else (if i = 6 then 43 else 0)) else (if i ≤ 7 then (if i = 7 then 53 else 0) else (if i ≤ 8 then (if i = 8 then 59 else 0) else (if i = 9 then 67 else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 71 else 0) else (if i = 11 then 73 else 0)) else (if i ≤ 12 then (if i = 12 then 83 else 0) else (if i ≤ 13 then (if i = 13 then 97 else 0) else (if i = 14 then 103 else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 109 else 0) else (if i = 16 then 127 else 0)) else (if i ≤ 17 then (if i = 17 then 137 else 0) else (if i ≤ 18 then (if i = 18 then 149 else 0) else (if i = 19 then 157 else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 167 else 0) else (if i = 21 then 181 else 0)) else (if i ≤ 22 then (if i = 22 then 197 else 0) else (if i ≤ 23 then (if i = 23 then 211 else 0) else (if i = 24 then 227 else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 233 else 0) else (if i = 26 then 251 else 0)) else (if i ≤ 27 then (if i = 27 then 269 else 0) else (if i ≤ 28 then (if i = 28 then 281 else 0) else (if i = 29 then 293 else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 313 else 0) else (if i = 31 then 337 else 0)) else (if i ≤ 32 then (if i = 32 then 353 else 0) else (if i ≤ 33 then (if i = 33 then 373 else 0) else (if i = 34 then 389 else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 409 else 0) else (if i = 36 then 431 else 0)) else (if i ≤ 37 then (if i = 37 then 443 else 0) else (if i ≤ 38 then (if i = 38 then 461 else 0) else (if i = 39 then 479 else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 499 else 0) else (if i = 41 then 521 else 0)) else (if i ≤ 42 then (if i = 42 then 541 else 0) else (if i ≤ 43 then (if i = 43 then 563 else 0) else (if i = 44 then 587 else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 607 else 0) else (if i = 46 then 631 else 0)) else (if i ≤ 47 then (if i = 47 then 653 else 0) else (if i ≤ 48 then (if i = 48 then 677 else 0) else (if i = 49 then 709 else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 739 else 0) else (if i = 51 then 757 else 0)) else (if i ≤ 52 then (if i = 52 then 773 else 0) else (if i ≤ 53 then (if i = 53 then 811 else 0) else (if i = 54 then 829 else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 859 else 0) else (if i = 56 then 883 else 0)) else (if i ≤ 57 then (if i = 57 then 911 else 0) else (if i ≤ 58 then (if i = 58 then 937 else 0) else (if i = 59 then 967 else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 991 else 0) else (if i = 61 then 1019 else 0)) else (if i ≤ 62 then (if i = 62 then 1039 else 0) else (if i ≤ 63 then (if i = 63 then 1063 else 0) else (if i = 64 then 1093 else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1117 else 0) else (if i = 66 then 1153 else 0)) else (if i ≤ 67 then (if i = 67 then 1187 else 0) else (if i ≤ 68 then (if i = 68 then 1217 else 0) else (if i = 69 then 1237 else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 1279 else 0) else (if i = 71 then 1297 else 0)) else (if i ≤ 72 then (if i = 72 then 1319 else 0) else (if i ≤ 73 then (if i = 73 then 1367 else 0) else (if i = 74 then 1409 else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 1433 else 0) else (if i = 76 then 1453 else 0)) else (if i ≤ 77 then (if i = 77 then 1483 else 0) else (if i ≤ 78 then (if i = 78 then 1499 else 0) else (if i = 79 then 1523 else 0))))))))

def blkNx : ℕ → ℕ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 19 else 0) else (if i = 1 then 23 else 0)) else (if i ≤ 2 then (if i = 2 then 29 else 0) else (if i ≤ 3 then (if i = 3 then 31 else 0) else (if i = 4 then 37 else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 43 else 0) else (if i = 6 then 47 else 0)) else (if i ≤ 7 then (if i = 7 then 59 else 0) else (if i ≤ 8 then (if i = 8 then 61 else 0) else (if i = 9 then 71 else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 73 else 0) else (if i = 11 then 79 else 0)) else (if i ≤ 12 then (if i = 12 then 89 else 0) else (if i ≤ 13 then (if i = 13 then 101 else 0) else (if i = 14 then 107 else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 113 else 0) else (if i = 16 then 131 else 0)) else (if i ≤ 17 then (if i = 17 then 139 else 0) else (if i ≤ 18 then (if i = 18 then 151 else 0) else (if i = 19 then 163 else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 173 else 0) else (if i = 21 then 191 else 0)) else (if i ≤ 22 then (if i = 22 then 199 else 0) else (if i ≤ 23 then (if i = 23 then 223 else 0) else (if i = 24 then 229 else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 239 else 0) else (if i = 26 then 257 else 0)) else (if i ≤ 27 then (if i = 27 then 271 else 0) else (if i ≤ 28 then (if i = 28 then 283 else 0) else (if i = 29 then 307 else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 317 else 0) else (if i = 31 then 347 else 0)) else (if i ≤ 32 then (if i = 32 then 359 else 0) else (if i ≤ 33 then (if i = 33 then 379 else 0) else (if i = 34 then 397 else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 419 else 0) else (if i = 36 then 433 else 0)) else (if i ≤ 37 then (if i = 37 then 449 else 0) else (if i ≤ 38 then (if i = 38 then 463 else 0) else (if i = 39 then 487 else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 503 else 0) else (if i = 41 then 523 else 0)) else (if i ≤ 42 then (if i = 42 then 547 else 0) else (if i ≤ 43 then (if i = 43 then 569 else 0) else (if i = 44 then 593 else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 613 else 0) else (if i = 46 then 641 else 0)) else (if i ≤ 47 then (if i = 47 then 659 else 0) else (if i ≤ 48 then (if i = 48 then 683 else 0) else (if i = 49 then 719 else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 743 else 0) else (if i = 51 then 761 else 0)) else (if i ≤ 52 then (if i = 52 then 787 else 0) else (if i ≤ 53 then (if i = 53 then 821 else 0) else (if i = 54 then 839 else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 863 else 0) else (if i = 56 then 887 else 0)) else (if i ≤ 57 then (if i = 57 then 919 else 0) else (if i ≤ 58 then (if i = 58 then 941 else 0) else (if i = 59 then 971 else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 997 else 0) else (if i = 61 then 1021 else 0)) else (if i ≤ 62 then (if i = 62 then 1049 else 0) else (if i ≤ 63 then (if i = 63 then 1069 else 0) else (if i = 64 then 1097 else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1123 else 0) else (if i = 66 then 1163 else 0)) else (if i ≤ 67 then (if i = 67 then 1193 else 0) else (if i ≤ 68 then (if i = 68 then 1223 else 0) else (if i = 69 then 1249 else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 1283 else 0) else (if i = 71 then 1301 else 0)) else (if i ≤ 72 then (if i = 72 then 1321 else 0) else (if i ≤ 73 then (if i = 73 then 1373 else 0) else (if i = 74 then 1423 else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 1439 else 0) else (if i = 76 then 1459 else 0)) else (if i ≤ 77 then (if i = 77 then 1487 else 0) else (if i ≤ 78 then (if i = 78 then 1511 else 0) else (if i = 79 then 1531 else 0))))))))

def blkLp : ℕ → ℕ → ℕ := fun i p =>
  if p = 2 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 5 else 1) else (if i = 1 then 5 else 1)) else (if i ≤ 2 then (if i = 2 then 6 else 1) else (if i ≤ 3 then (if i = 3 then 6 else 1) else (if i = 4 then 6 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 6 else 1) else (if i = 6 then 7 else 1)) else (if i ≤ 7 then (if i = 7 then 7 else 1) else (if i ≤ 8 then (if i = 8 then 7 else 1) else (if i = 9 then 7 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 7 else 1) else (if i = 11 then 7 else 1)) else (if i ≤ 12 then (if i = 12 then 8 else 1) else (if i ≤ 13 then (if i = 13 then 8 else 1) else (if i = 14 then 8 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 8 else 1) else (if i = 16 then 8 else 1)) else (if i ≤ 17 then (if i = 17 then 8 else 1) else (if i ≤ 18 then (if i = 18 then 9 else 1) else (if i = 19 then 9 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 9 else 1) else (if i = 21 then 9 else 1)) else (if i ≤ 22 then (if i = 22 then 9 else 1) else (if i ≤ 23 then (if i = 23 then 9 else 1) else (if i = 24 then 9 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 9 else 1) else (if i = 26 then 10 else 1)) else (if i ≤ 27 then (if i = 27 then 10 else 1) else (if i ≤ 28 then (if i = 28 then 10 else 1) else (if i = 29 then 10 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 10 else 1) else (if i = 31 then 10 else 1)) else (if i ≤ 32 then (if i = 32 then 10 else 1) else (if i ≤ 33 then (if i = 33 then 10 else 1) else (if i = 34 then 10 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 10 else 1) else (if i = 36 then 10 else 1)) else (if i ≤ 37 then (if i = 37 then 10 else 1) else (if i ≤ 38 then (if i = 38 then 11 else 1) else (if i = 39 then 11 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 11 else 1) else (if i = 41 then 11 else 1)) else (if i ≤ 42 then (if i = 42 then 11 else 1) else (if i ≤ 43 then (if i = 43 then 11 else 1) else (if i = 44 then 11 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 11 else 1) else (if i = 46 then 11 else 1)) else (if i ≤ 47 then (if i = 47 then 11 else 1) else (if i ≤ 48 then (if i = 48 then 11 else 1) else (if i = 49 then 11 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 11 else 1) else (if i = 51 then 11 else 1)) else (if i ≤ 52 then (if i = 52 then 11 else 1) else (if i ≤ 53 then (if i = 53 then 11 else 1) else (if i = 54 then 11 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 12 else 1) else (if i = 56 then 12 else 1)) else (if i ≤ 57 then (if i = 57 then 12 else 1) else (if i ≤ 58 then (if i = 58 then 12 else 1) else (if i = 59 then 12 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 12 else 1) else (if i = 61 then 12 else 1)) else (if i ≤ 62 then (if i = 62 then 12 else 1) else (if i ≤ 63 then (if i = 63 then 12 else 1) else (if i = 64 then 12 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 12 else 1) else (if i = 66 then 12 else 1)) else (if i ≤ 67 then (if i = 67 then 12 else 1) else (if i ≤ 68 then (if i = 68 then 12 else 1) else (if i = 69 then 12 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 12 else 1) else (if i = 71 then 12 else 1)) else (if i ≤ 72 then (if i = 72 then 12 else 1) else (if i ≤ 73 then (if i = 73 then 12 else 1) else (if i = 74 then 12 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 12 else 1) else (if i = 76 then 12 else 1)) else (if i ≤ 77 then (if i = 77 then 12 else 1) else (if i ≤ 78 then (if i = 78 then 12 else 1) else (if i = 79 then 12 else 1)))))))) else
  if p = 3 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 3 else 1) else (if i = 1 then 3 else 1)) else (if i ≤ 2 then (if i = 2 then 3 else 1) else (if i ≤ 3 then (if i = 3 then 3 else 1) else (if i = 4 then 4 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 4 else 1) else (if i = 6 then 4 else 1)) else (if i ≤ 7 then (if i = 7 then 4 else 1) else (if i ≤ 8 then (if i = 8 then 4 else 1) else (if i = 9 then 4 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 4 else 1) else (if i = 11 then 4 else 1)) else (if i ≤ 12 then (if i = 12 then 5 else 1) else (if i ≤ 13 then (if i = 13 then 5 else 1) else (if i = 14 then 5 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 5 else 1) else (if i = 16 then 5 else 1)) else (if i ≤ 17 then (if i = 17 then 5 else 1) else (if i ≤ 18 then (if i = 18 then 5 else 1) else (if i = 19 then 5 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 5 else 1) else (if i = 21 then 5 else 1)) else (if i ≤ 22 then (if i = 22 then 5 else 1) else (if i ≤ 23 then (if i = 23 then 6 else 1) else (if i = 24 then 6 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 6 else 1) else (if i = 26 then 6 else 1)) else (if i ≤ 27 then (if i = 27 then 6 else 1) else (if i ≤ 28 then (if i = 28 then 6 else 1) else (if i = 29 then 6 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 6 else 1) else (if i = 31 then 6 else 1)) else (if i ≤ 32 then (if i = 32 then 6 else 1) else (if i ≤ 33 then (if i = 33 then 6 else 1) else (if i = 34 then 6 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 6 else 1) else (if i = 36 then 6 else 1)) else (if i ≤ 37 then (if i = 37 then 6 else 1) else (if i ≤ 38 then (if i = 38 then 6 else 1) else (if i = 39 then 6 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 6 else 1) else (if i = 41 then 6 else 1)) else (if i ≤ 42 then (if i = 42 then 6 else 1) else (if i ≤ 43 then (if i = 43 then 7 else 1) else (if i = 44 then 7 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 7 else 1) else (if i = 46 then 7 else 1)) else (if i ≤ 47 then (if i = 47 then 7 else 1) else (if i ≤ 48 then (if i = 48 then 7 else 1) else (if i = 49 then 7 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 7 else 1) else (if i = 51 then 7 else 1)) else (if i ≤ 52 then (if i = 52 then 7 else 1) else (if i ≤ 53 then (if i = 53 then 7 else 1) else (if i = 54 then 7 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 7 else 1) else (if i = 56 then 7 else 1)) else (if i ≤ 57 then (if i = 57 then 7 else 1) else (if i ≤ 58 then (if i = 58 then 7 else 1) else (if i = 59 then 7 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 7 else 1) else (if i = 61 then 7 else 1)) else (if i ≤ 62 then (if i = 62 then 7 else 1) else (if i ≤ 63 then (if i = 63 then 7 else 1) else (if i = 64 then 7 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 7 else 1) else (if i = 66 then 7 else 1)) else (if i ≤ 67 then (if i = 67 then 7 else 1) else (if i ≤ 68 then (if i = 68 then 7 else 1) else (if i = 69 then 7 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 7 else 1) else (if i = 71 then 7 else 1)) else (if i ≤ 72 then (if i = 72 then 7 else 1) else (if i ≤ 73 then (if i = 73 then 7 else 1) else (if i = 74 then 7 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 7 else 1) else (if i = 76 then 7 else 1)) else (if i ≤ 77 then (if i = 77 then 8 else 1) else (if i ≤ 78 then (if i = 78 then 8 else 1) else (if i = 79 then 8 else 1)))))))) else
  if p = 5 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 2 else 1) else (if i = 1 then 2 else 1)) else (if i ≤ 2 then (if i = 2 then 2 else 1) else (if i ≤ 3 then (if i = 3 then 2 else 1) else (if i = 4 then 2 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 2 else 1) else (if i = 6 then 2 else 1)) else (if i ≤ 7 then (if i = 7 then 2 else 1) else (if i ≤ 8 then (if i = 8 then 3 else 1) else (if i = 9 then 3 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 3 else 1) else (if i = 11 then 3 else 1)) else (if i ≤ 12 then (if i = 12 then 3 else 1) else (if i ≤ 13 then (if i = 13 then 3 else 1) else (if i = 14 then 3 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 3 else 1) else (if i = 16 then 3 else 1)) else (if i ≤ 17 then (if i = 17 then 3 else 1) else (if i ≤ 18 then (if i = 18 then 3 else 1) else (if i = 19 then 3 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 3 else 1) else (if i = 21 then 3 else 1)) else (if i ≤ 22 then (if i = 22 then 3 else 1) else (if i ≤ 23 then (if i = 23 then 3 else 1) else (if i = 24 then 3 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 4 else 1) else (if i = 26 then 4 else 1)) else (if i ≤ 27 then (if i = 27 then 4 else 1) else (if i ≤ 28 then (if i = 28 then 4 else 1) else (if i = 29 then 4 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 4 else 1) else (if i = 31 then 4 else 1)) else (if i ≤ 32 then (if i = 32 then 4 else 1) else (if i ≤ 33 then (if i = 33 then 4 else 1) else (if i = 34 then 4 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 4 else 1) else (if i = 36 then 4 else 1)) else (if i ≤ 37 then (if i = 37 then 4 else 1) else (if i ≤ 38 then (if i = 38 then 4 else 1) else (if i = 39 then 4 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 4 else 1) else (if i = 41 then 4 else 1)) else (if i ≤ 42 then (if i = 42 then 4 else 1) else (if i ≤ 43 then (if i = 43 then 4 else 1) else (if i = 44 then 4 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 4 else 1) else (if i = 46 then 4 else 1)) else (if i ≤ 47 then (if i = 47 then 4 else 1) else (if i ≤ 48 then (if i = 48 then 4 else 1) else (if i = 49 then 4 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 4 else 1) else (if i = 51 then 4 else 1)) else (if i ≤ 52 then (if i = 52 then 4 else 1) else (if i ≤ 53 then (if i = 53 then 4 else 1) else (if i = 54 then 4 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 4 else 1) else (if i = 56 then 4 else 1)) else (if i ≤ 57 then (if i = 57 then 4 else 1) else (if i ≤ 58 then (if i = 58 then 5 else 1) else (if i = 59 then 5 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 5 else 1) else (if i = 61 then 5 else 1)) else (if i ≤ 62 then (if i = 62 then 5 else 1) else (if i ≤ 63 then (if i = 63 then 5 else 1) else (if i = 64 then 5 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 5 else 1) else (if i = 66 then 5 else 1)) else (if i ≤ 67 then (if i = 67 then 5 else 1) else (if i ≤ 68 then (if i = 68 then 5 else 1) else (if i = 69 then 5 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 5 else 1) else (if i = 71 then 5 else 1)) else (if i ≤ 72 then (if i = 72 then 5 else 1) else (if i ≤ 73 then (if i = 73 then 5 else 1) else (if i = 74 then 5 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 5 else 1) else (if i = 76 then 5 else 1)) else (if i ≤ 77 then (if i = 77 then 5 else 1) else (if i ≤ 78 then (if i = 78 then 5 else 1) else (if i = 79 then 5 else 1)))))))) else
  if p = 7 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 2 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 2 else 1) else (if i = 6 then 2 else 1)) else (if i ≤ 7 then (if i = 7 then 2 else 1) else (if i ≤ 8 then (if i = 8 then 2 else 1) else (if i = 9 then 2 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 2 else 1) else (if i = 11 then 2 else 1)) else (if i ≤ 12 then (if i = 12 then 2 else 1) else (if i ≤ 13 then (if i = 13 then 2 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 3 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 3 else 1) else (if i = 21 then 3 else 1)) else (if i ≤ 22 then (if i = 22 then 3 else 1) else (if i ≤ 23 then (if i = 23 then 3 else 1) else (if i = 24 then 3 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 3 else 1) else (if i = 26 then 3 else 1)) else (if i ≤ 27 then (if i = 27 then 3 else 1) else (if i ≤ 28 then (if i = 28 then 3 else 1) else (if i = 29 then 3 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 3 else 1) else (if i = 31 then 3 else 1)) else (if i ≤ 32 then (if i = 32 then 3 else 1) else (if i ≤ 33 then (if i = 33 then 3 else 1) else (if i = 34 then 3 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 3 else 1) else (if i = 36 then 3 else 1)) else (if i ≤ 37 then (if i = 37 then 3 else 1) else (if i ≤ 38 then (if i = 38 then 3 else 1) else (if i = 39 then 3 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 3 else 1) else (if i = 41 then 3 else 1)) else (if i ≤ 42 then (if i = 42 then 3 else 1) else (if i ≤ 43 then (if i = 43 then 3 else 1) else (if i = 44 then 3 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 3 else 1) else (if i = 46 then 3 else 1)) else (if i ≤ 47 then (if i = 47 then 3 else 1) else (if i ≤ 48 then (if i = 48 then 3 else 1) else (if i = 49 then 3 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 3 else 1) else (if i = 51 then 3 else 1)) else (if i ≤ 52 then (if i = 52 then 3 else 1) else (if i ≤ 53 then (if i = 53 then 4 else 1) else (if i = 54 then 4 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 4 else 1) else (if i = 56 then 4 else 1)) else (if i ≤ 57 then (if i = 57 then 4 else 1) else (if i ≤ 58 then (if i = 58 then 4 else 1) else (if i = 59 then 4 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 4 else 1) else (if i = 61 then 4 else 1)) else (if i ≤ 62 then (if i = 62 then 4 else 1) else (if i ≤ 63 then (if i = 63 then 4 else 1) else (if i = 64 then 4 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 4 else 1) else (if i = 66 then 4 else 1)) else (if i ≤ 67 then (if i = 67 then 4 else 1) else (if i ≤ 68 then (if i = 68 then 4 else 1) else (if i = 69 then 4 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 4 else 1) else (if i = 71 then 4 else 1)) else (if i ≤ 72 then (if i = 72 then 4 else 1) else (if i ≤ 73 then (if i = 73 then 4 else 1) else (if i = 74 then 4 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 4 else 1) else (if i = 76 then 4 else 1)) else (if i ≤ 77 then (if i = 77 then 4 else 1) else (if i ≤ 78 then (if i = 78 then 4 else 1) else (if i = 79 then 4 else 1)))))))) else
  if p = 11 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 2 else 1)) else (if i ≤ 12 then (if i = 12 then 2 else 1) else (if i ≤ 13 then (if i = 13 then 2 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 2 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 3 else 1) else (if i = 44 then 3 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 3 else 1) else (if i = 46 then 3 else 1)) else (if i ≤ 47 then (if i = 47 then 3 else 1) else (if i ≤ 48 then (if i = 48 then 3 else 1) else (if i = 49 then 3 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 3 else 1) else (if i = 51 then 3 else 1)) else (if i ≤ 52 then (if i = 52 then 3 else 1) else (if i ≤ 53 then (if i = 53 then 3 else 1) else (if i = 54 then 3 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 3 else 1) else (if i = 56 then 3 else 1)) else (if i ≤ 57 then (if i = 57 then 3 else 1) else (if i ≤ 58 then (if i = 58 then 3 else 1) else (if i = 59 then 3 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 3 else 1) else (if i = 61 then 3 else 1)) else (if i ≤ 62 then (if i = 62 then 3 else 1) else (if i ≤ 63 then (if i = 63 then 3 else 1) else (if i = 64 then 3 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 3 else 1) else (if i = 66 then 3 else 1)) else (if i ≤ 67 then (if i = 67 then 3 else 1) else (if i ≤ 68 then (if i = 68 then 3 else 1) else (if i = 69 then 3 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 3 else 1) else (if i = 71 then 3 else 1)) else (if i ≤ 72 then (if i = 72 then 3 else 1) else (if i ≤ 73 then (if i = 73 then 3 else 1) else (if i = 74 then 3 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 3 else 1) else (if i = 76 then 3 else 1)) else (if i ≤ 77 then (if i = 77 then 3 else 1) else (if i ≤ 78 then (if i = 78 then 3 else 1) else (if i = 79 then 3 else 1)))))))) else
  if p = 13 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 2 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 2 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 3 else 1) else (if i ≤ 58 then (if i = 58 then 3 else 1) else (if i = 59 then 3 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 3 else 1) else (if i = 61 then 3 else 1)) else (if i ≤ 62 then (if i = 62 then 3 else 1) else (if i ≤ 63 then (if i = 63 then 3 else 1) else (if i = 64 then 3 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 3 else 1) else (if i = 66 then 3 else 1)) else (if i ≤ 67 then (if i = 67 then 3 else 1) else (if i ≤ 68 then (if i = 68 then 3 else 1) else (if i = 69 then 3 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 3 else 1) else (if i = 71 then 3 else 1)) else (if i ≤ 72 then (if i = 72 then 3 else 1) else (if i ≤ 73 then (if i = 73 then 3 else 1) else (if i = 74 then 3 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 3 else 1) else (if i = 76 then 3 else 1)) else (if i ≤ 77 then (if i = 77 then 3 else 1) else (if i ≤ 78 then (if i = 78 then 3 else 1) else (if i = 79 then 3 else 1)))))))) else
  if p = 17 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 19 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 23 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 29 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 31 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 37 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 41 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 43 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 1 else 1) else (if i = 59 then 1 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 1 else 1) else (if i = 61 then 1 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else if p = 47 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 1 else 1) else (if i = 59 then 1 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 1 else 1) else (if i = 61 then 1 else 1)) else (if i ≤ 62 then (if i = 62 then 1 else 1) else (if i ≤ 63 then (if i = 63 then 1 else 1) else (if i = 64 then 1 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1 else 1) else (if i = 66 then 1 else 1)) else (if i ≤ 67 then (if i = 67 then 1 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else 1

def blkMp : ℕ → ℕ → ℕ := fun i p =>
  if p = 2 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 5 else 1) else (if i = 1 then 5 else 1)) else (if i ≤ 2 then (if i = 2 then 5 else 1) else (if i ≤ 3 then (if i = 3 then 6 else 1) else (if i = 4 then 6 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 6 else 1) else (if i = 6 then 6 else 1)) else (if i ≤ 7 then (if i = 7 then 7 else 1) else (if i ≤ 8 then (if i = 8 then 7 else 1) else (if i = 9 then 7 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 7 else 1) else (if i = 11 then 7 else 1)) else (if i ≤ 12 then (if i = 12 then 7 else 1) else (if i ≤ 13 then (if i = 13 then 8 else 1) else (if i = 14 then 8 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 8 else 1) else (if i = 16 then 8 else 1)) else (if i ≤ 17 then (if i = 17 then 8 else 1) else (if i ≤ 18 then (if i = 18 then 8 else 1) else (if i = 19 then 9 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 9 else 1) else (if i = 21 then 9 else 1)) else (if i ≤ 22 then (if i = 22 then 9 else 1) else (if i ≤ 23 then (if i = 23 then 9 else 1) else (if i = 24 then 9 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 9 else 1) else (if i = 26 then 9 else 1)) else (if i ≤ 27 then (if i = 27 then 10 else 1) else (if i ≤ 28 then (if i = 28 then 10 else 1) else (if i = 29 then 10 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 10 else 1) else (if i = 31 then 10 else 1)) else (if i ≤ 32 then (if i = 32 then 10 else 1) else (if i ≤ 33 then (if i = 33 then 10 else 1) else (if i = 34 then 10 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 10 else 1) else (if i = 36 then 10 else 1)) else (if i ≤ 37 then (if i = 37 then 10 else 1) else (if i ≤ 38 then (if i = 38 then 10 else 1) else (if i = 39 then 11 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 11 else 1) else (if i = 41 then 11 else 1)) else (if i ≤ 42 then (if i = 42 then 11 else 1) else (if i ≤ 43 then (if i = 43 then 11 else 1) else (if i = 44 then 11 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 11 else 1) else (if i = 46 then 11 else 1)) else (if i ≤ 47 then (if i = 47 then 11 else 1) else (if i ≤ 48 then (if i = 48 then 11 else 1) else (if i = 49 then 11 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 11 else 1) else (if i = 51 then 11 else 1)) else (if i ≤ 52 then (if i = 52 then 11 else 1) else (if i ≤ 53 then (if i = 53 then 11 else 1) else (if i = 54 then 11 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 11 else 1) else (if i = 56 then 12 else 1)) else (if i ≤ 57 then (if i = 57 then 12 else 1) else (if i ≤ 58 then (if i = 58 then 12 else 1) else (if i = 59 then 12 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 12 else 1) else (if i = 61 then 12 else 1)) else (if i ≤ 62 then (if i = 62 then 12 else 1) else (if i ≤ 63 then (if i = 63 then 12 else 1) else (if i = 64 then 12 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 12 else 1) else (if i = 66 then 12 else 1)) else (if i ≤ 67 then (if i = 67 then 12 else 1) else (if i ≤ 68 then (if i = 68 then 12 else 1) else (if i = 69 then 12 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 12 else 1) else (if i = 71 then 12 else 1)) else (if i ≤ 72 then (if i = 72 then 12 else 1) else (if i ≤ 73 then (if i = 73 then 12 else 1) else (if i = 74 then 12 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 12 else 1) else (if i = 76 then 12 else 1)) else (if i ≤ 77 then (if i = 77 then 12 else 1) else (if i ≤ 78 then (if i = 78 then 12 else 1) else (if i = 79 then 12 else 1)))))))) else
  if p = 3 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 3 else 1) else (if i = 1 then 3 else 1)) else (if i ≤ 2 then (if i = 2 then 3 else 1) else (if i ≤ 3 then (if i = 3 then 3 else 1) else (if i = 4 then 3 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 4 else 1) else (if i = 6 then 4 else 1)) else (if i ≤ 7 then (if i = 7 then 4 else 1) else (if i ≤ 8 then (if i = 8 then 4 else 1) else (if i = 9 then 4 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 4 else 1) else (if i = 11 then 4 else 1)) else (if i ≤ 12 then (if i = 12 then 4 else 1) else (if i ≤ 13 then (if i = 13 then 5 else 1) else (if i = 14 then 5 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 5 else 1) else (if i = 16 then 5 else 1)) else (if i ≤ 17 then (if i = 17 then 5 else 1) else (if i ≤ 18 then (if i = 18 then 5 else 1) else (if i = 19 then 5 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 5 else 1) else (if i = 21 then 5 else 1)) else (if i ≤ 22 then (if i = 22 then 5 else 1) else (if i ≤ 23 then (if i = 23 then 5 else 1) else (if i = 24 then 6 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 6 else 1) else (if i = 26 then 6 else 1)) else (if i ≤ 27 then (if i = 27 then 6 else 1) else (if i ≤ 28 then (if i = 28 then 6 else 1) else (if i = 29 then 6 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 6 else 1) else (if i = 31 then 6 else 1)) else (if i ≤ 32 then (if i = 32 then 6 else 1) else (if i ≤ 33 then (if i = 33 then 6 else 1) else (if i = 34 then 6 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 6 else 1) else (if i = 36 then 6 else 1)) else (if i ≤ 37 then (if i = 37 then 6 else 1) else (if i ≤ 38 then (if i = 38 then 6 else 1) else (if i = 39 then 6 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 6 else 1) else (if i = 41 then 6 else 1)) else (if i ≤ 42 then (if i = 42 then 6 else 1) else (if i ≤ 43 then (if i = 43 then 6 else 1) else (if i = 44 then 7 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 7 else 1) else (if i = 46 then 7 else 1)) else (if i ≤ 47 then (if i = 47 then 7 else 1) else (if i ≤ 48 then (if i = 48 then 7 else 1) else (if i = 49 then 7 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 7 else 1) else (if i = 51 then 7 else 1)) else (if i ≤ 52 then (if i = 52 then 7 else 1) else (if i ≤ 53 then (if i = 53 then 7 else 1) else (if i = 54 then 7 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 7 else 1) else (if i = 56 then 7 else 1)) else (if i ≤ 57 then (if i = 57 then 7 else 1) else (if i ≤ 58 then (if i = 58 then 7 else 1) else (if i = 59 then 7 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 7 else 1) else (if i = 61 then 7 else 1)) else (if i ≤ 62 then (if i = 62 then 7 else 1) else (if i ≤ 63 then (if i = 63 then 7 else 1) else (if i = 64 then 7 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 7 else 1) else (if i = 66 then 7 else 1)) else (if i ≤ 67 then (if i = 67 then 7 else 1) else (if i ≤ 68 then (if i = 68 then 7 else 1) else (if i = 69 then 7 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 7 else 1) else (if i = 71 then 7 else 1)) else (if i ≤ 72 then (if i = 72 then 7 else 1) else (if i ≤ 73 then (if i = 73 then 7 else 1) else (if i = 74 then 7 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 7 else 1) else (if i = 76 then 7 else 1)) else (if i ≤ 77 then (if i = 77 then 7 else 1) else (if i ≤ 78 then (if i = 78 then 8 else 1) else (if i = 79 then 8 else 1)))))))) else
  if p = 5 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 2 else 1) else (if i = 1 then 2 else 1)) else (if i ≤ 2 then (if i = 2 then 2 else 1) else (if i ≤ 3 then (if i = 3 then 2 else 1) else (if i = 4 then 2 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 2 else 1) else (if i = 6 then 2 else 1)) else (if i ≤ 7 then (if i = 7 then 2 else 1) else (if i ≤ 8 then (if i = 8 then 2 else 1) else (if i = 9 then 3 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 3 else 1) else (if i = 11 then 3 else 1)) else (if i ≤ 12 then (if i = 12 then 3 else 1) else (if i ≤ 13 then (if i = 13 then 3 else 1) else (if i = 14 then 3 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 3 else 1) else (if i = 16 then 3 else 1)) else (if i ≤ 17 then (if i = 17 then 3 else 1) else (if i ≤ 18 then (if i = 18 then 3 else 1) else (if i = 19 then 3 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 3 else 1) else (if i = 21 then 3 else 1)) else (if i ≤ 22 then (if i = 22 then 3 else 1) else (if i ≤ 23 then (if i = 23 then 3 else 1) else (if i = 24 then 3 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 3 else 1) else (if i = 26 then 4 else 1)) else (if i ≤ 27 then (if i = 27 then 4 else 1) else (if i ≤ 28 then (if i = 28 then 4 else 1) else (if i = 29 then 4 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 4 else 1) else (if i = 31 then 4 else 1)) else (if i ≤ 32 then (if i = 32 then 4 else 1) else (if i ≤ 33 then (if i = 33 then 4 else 1) else (if i = 34 then 4 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 4 else 1) else (if i = 36 then 4 else 1)) else (if i ≤ 37 then (if i = 37 then 4 else 1) else (if i ≤ 38 then (if i = 38 then 4 else 1) else (if i = 39 then 4 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 4 else 1) else (if i = 41 then 4 else 1)) else (if i ≤ 42 then (if i = 42 then 4 else 1) else (if i ≤ 43 then (if i = 43 then 4 else 1) else (if i = 44 then 4 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 4 else 1) else (if i = 46 then 4 else 1)) else (if i ≤ 47 then (if i = 47 then 4 else 1) else (if i ≤ 48 then (if i = 48 then 4 else 1) else (if i = 49 then 4 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 4 else 1) else (if i = 51 then 4 else 1)) else (if i ≤ 52 then (if i = 52 then 4 else 1) else (if i ≤ 53 then (if i = 53 then 4 else 1) else (if i = 54 then 4 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 4 else 1) else (if i = 56 then 4 else 1)) else (if i ≤ 57 then (if i = 57 then 4 else 1) else (if i ≤ 58 then (if i = 58 then 4 else 1) else (if i = 59 then 5 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 5 else 1) else (if i = 61 then 5 else 1)) else (if i ≤ 62 then (if i = 62 then 5 else 1) else (if i ≤ 63 then (if i = 63 then 5 else 1) else (if i = 64 then 5 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 5 else 1) else (if i = 66 then 5 else 1)) else (if i ≤ 67 then (if i = 67 then 5 else 1) else (if i ≤ 68 then (if i = 68 then 5 else 1) else (if i = 69 then 5 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 5 else 1) else (if i = 71 then 5 else 1)) else (if i ≤ 72 then (if i = 72 then 5 else 1) else (if i ≤ 73 then (if i = 73 then 5 else 1) else (if i = 74 then 5 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 5 else 1) else (if i = 76 then 5 else 1)) else (if i ≤ 77 then (if i = 77 then 5 else 1) else (if i ≤ 78 then (if i = 78 then 5 else 1) else (if i = 79 then 5 else 1)))))))) else
  if p = 7 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 2 else 1) else (if i = 6 then 2 else 1)) else (if i ≤ 7 then (if i = 7 then 2 else 1) else (if i ≤ 8 then (if i = 8 then 2 else 1) else (if i = 9 then 2 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 2 else 1) else (if i = 11 then 2 else 1)) else (if i ≤ 12 then (if i = 12 then 2 else 1) else (if i ≤ 13 then (if i = 13 then 2 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 2 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 3 else 1) else (if i = 21 then 3 else 1)) else (if i ≤ 22 then (if i = 22 then 3 else 1) else (if i ≤ 23 then (if i = 23 then 3 else 1) else (if i = 24 then 3 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 3 else 1) else (if i = 26 then 3 else 1)) else (if i ≤ 27 then (if i = 27 then 3 else 1) else (if i ≤ 28 then (if i = 28 then 3 else 1) else (if i = 29 then 3 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 3 else 1) else (if i = 31 then 3 else 1)) else (if i ≤ 32 then (if i = 32 then 3 else 1) else (if i ≤ 33 then (if i = 33 then 3 else 1) else (if i = 34 then 3 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 3 else 1) else (if i = 36 then 3 else 1)) else (if i ≤ 37 then (if i = 37 then 3 else 1) else (if i ≤ 38 then (if i = 38 then 3 else 1) else (if i = 39 then 3 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 3 else 1) else (if i = 41 then 3 else 1)) else (if i ≤ 42 then (if i = 42 then 3 else 1) else (if i ≤ 43 then (if i = 43 then 3 else 1) else (if i = 44 then 3 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 3 else 1) else (if i = 46 then 3 else 1)) else (if i ≤ 47 then (if i = 47 then 3 else 1) else (if i ≤ 48 then (if i = 48 then 3 else 1) else (if i = 49 then 3 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 3 else 1) else (if i = 51 then 3 else 1)) else (if i ≤ 52 then (if i = 52 then 3 else 1) else (if i ≤ 53 then (if i = 53 then 3 else 1) else (if i = 54 then 4 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 4 else 1) else (if i = 56 then 4 else 1)) else (if i ≤ 57 then (if i = 57 then 4 else 1) else (if i ≤ 58 then (if i = 58 then 4 else 1) else (if i = 59 then 4 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 4 else 1) else (if i = 61 then 4 else 1)) else (if i ≤ 62 then (if i = 62 then 4 else 1) else (if i ≤ 63 then (if i = 63 then 4 else 1) else (if i = 64 then 4 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 4 else 1) else (if i = 66 then 4 else 1)) else (if i ≤ 67 then (if i = 67 then 4 else 1) else (if i ≤ 68 then (if i = 68 then 4 else 1) else (if i = 69 then 4 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 4 else 1) else (if i = 71 then 4 else 1)) else (if i ≤ 72 then (if i = 72 then 4 else 1) else (if i ≤ 73 then (if i = 73 then 4 else 1) else (if i = 74 then 4 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 4 else 1) else (if i = 76 then 4 else 1)) else (if i ≤ 77 then (if i = 77 then 4 else 1) else (if i ≤ 78 then (if i = 78 then 4 else 1) else (if i = 79 then 4 else 1)))))))) else
  if p = 11 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 2 else 1) else (if i ≤ 13 then (if i = 13 then 2 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 2 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 3 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 3 else 1) else (if i = 46 then 3 else 1)) else (if i ≤ 47 then (if i = 47 then 3 else 1) else (if i ≤ 48 then (if i = 48 then 3 else 1) else (if i = 49 then 3 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 3 else 1) else (if i = 51 then 3 else 1)) else (if i ≤ 52 then (if i = 52 then 3 else 1) else (if i ≤ 53 then (if i = 53 then 3 else 1) else (if i = 54 then 3 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 3 else 1) else (if i = 56 then 3 else 1)) else (if i ≤ 57 then (if i = 57 then 3 else 1) else (if i ≤ 58 then (if i = 58 then 3 else 1) else (if i = 59 then 3 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 3 else 1) else (if i = 61 then 3 else 1)) else (if i ≤ 62 then (if i = 62 then 3 else 1) else (if i ≤ 63 then (if i = 63 then 3 else 1) else (if i = 64 then 3 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 3 else 1) else (if i = 66 then 3 else 1)) else (if i ≤ 67 then (if i = 67 then 3 else 1) else (if i ≤ 68 then (if i = 68 then 3 else 1) else (if i = 69 then 3 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 3 else 1) else (if i = 71 then 3 else 1)) else (if i ≤ 72 then (if i = 72 then 3 else 1) else (if i ≤ 73 then (if i = 73 then 3 else 1) else (if i = 74 then 3 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 3 else 1) else (if i = 76 then 3 else 1)) else (if i ≤ 77 then (if i = 77 then 3 else 1) else (if i ≤ 78 then (if i = 78 then 3 else 1) else (if i = 79 then 3 else 1)))))))) else
  if p = 13 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 2 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2 else 1) else (if i = 16 then 2 else 1)) else (if i ≤ 17 then (if i = 17 then 2 else 1) else (if i ≤ 18 then (if i = 18 then 2 else 1) else (if i = 19 then 2 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 3 else 1) else (if i = 59 then 3 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 3 else 1) else (if i = 61 then 3 else 1)) else (if i ≤ 62 then (if i = 62 then 3 else 1) else (if i ≤ 63 then (if i = 63 then 3 else 1) else (if i = 64 then 3 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 3 else 1) else (if i = 66 then 3 else 1)) else (if i ≤ 67 then (if i = 67 then 3 else 1) else (if i ≤ 68 then (if i = 68 then 3 else 1) else (if i = 69 then 3 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 3 else 1) else (if i = 71 then 3 else 1)) else (if i ≤ 72 then (if i = 72 then 3 else 1) else (if i ≤ 73 then (if i = 73 then 3 else 1) else (if i = 74 then 3 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 3 else 1) else (if i = 76 then 3 else 1)) else (if i ≤ 77 then (if i = 77 then 3 else 1) else (if i ≤ 78 then (if i = 78 then 3 else 1) else (if i = 79 then 3 else 1)))))))) else
  if p = 17 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 2 else 1)) else (if i ≤ 22 then (if i = 22 then 2 else 1) else (if i ≤ 23 then (if i = 23 then 2 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 19 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 2 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2 else 1) else (if i = 26 then 2 else 1)) else (if i ≤ 27 then (if i = 27 then 2 else 1) else (if i ≤ 28 then (if i = 28 then 2 else 1) else (if i = 29 then 2 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 23 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2 else 1) else (if i = 31 then 2 else 1)) else (if i ≤ 32 then (if i = 32 then 2 else 1) else (if i ≤ 33 then (if i = 33 then 2 else 1) else (if i = 34 then 2 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2 else 1) else (if i = 36 then 2 else 1)) else (if i ≤ 37 then (if i = 37 then 2 else 1) else (if i ≤ 38 then (if i = 38 then 2 else 1) else (if i = 39 then 2 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 29 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2 else 1) else (if i = 41 then 2 else 1)) else (if i ≤ 42 then (if i = 42 then 2 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 31 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 2 else 1) else (if i = 44 then 2 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2 else 1) else (if i = 46 then 2 else 1)) else (if i ≤ 47 then (if i = 47 then 2 else 1) else (if i ≤ 48 then (if i = 48 then 2 else 1) else (if i = 49 then 2 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2 else 1) else (if i = 51 then 2 else 1)) else (if i ≤ 52 then (if i = 52 then 2 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 37 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 2 else 1) else (if i = 54 then 2 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2 else 1) else (if i = 56 then 2 else 1)) else (if i ≤ 57 then (if i = 57 then 2 else 1) else (if i ≤ 58 then (if i = 58 then 2 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 41 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 1 else 1) else (if i = 59 then 2 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2 else 1) else (if i = 61 then 2 else 1)) else (if i ≤ 62 then (if i = 62 then 2 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else
  if p = 43 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 1 else 1) else (if i = 59 then 1 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 1 else 1) else (if i = 61 then 1 else 1)) else (if i ≤ 62 then (if i = 62 then 1 else 1) else (if i ≤ 63 then (if i = 63 then 2 else 1) else (if i = 64 then 2 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2 else 1) else (if i = 66 then 2 else 1)) else (if i ≤ 67 then (if i = 67 then 2 else 1) else (if i ≤ 68 then (if i = 68 then 2 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else if p = 47 then (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1 else 1) else (if i = 1 then 1 else 1)) else (if i ≤ 2 then (if i = 2 then 1 else 1) else (if i ≤ 3 then (if i = 3 then 1 else 1) else (if i = 4 then 1 else 1)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1 else 1) else (if i = 6 then 1 else 1)) else (if i ≤ 7 then (if i = 7 then 1 else 1) else (if i ≤ 8 then (if i = 8 then 1 else 1) else (if i = 9 then 1 else 1))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 1 else 1) else (if i = 11 then 1 else 1)) else (if i ≤ 12 then (if i = 12 then 1 else 1) else (if i ≤ 13 then (if i = 13 then 1 else 1) else (if i = 14 then 1 else 1)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 1 else 1) else (if i = 16 then 1 else 1)) else (if i ≤ 17 then (if i = 17 then 1 else 1) else (if i ≤ 18 then (if i = 18 then 1 else 1) else (if i = 19 then 1 else 1)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 1 else 1) else (if i = 21 then 1 else 1)) else (if i ≤ 22 then (if i = 22 then 1 else 1) else (if i ≤ 23 then (if i = 23 then 1 else 1) else (if i = 24 then 1 else 1)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 1 else 1) else (if i = 26 then 1 else 1)) else (if i ≤ 27 then (if i = 27 then 1 else 1) else (if i ≤ 28 then (if i = 28 then 1 else 1) else (if i = 29 then 1 else 1))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 1 else 1) else (if i = 31 then 1 else 1)) else (if i ≤ 32 then (if i = 32 then 1 else 1) else (if i ≤ 33 then (if i = 33 then 1 else 1) else (if i = 34 then 1 else 1)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 1 else 1) else (if i = 36 then 1 else 1)) else (if i ≤ 37 then (if i = 37 then 1 else 1) else (if i ≤ 38 then (if i = 38 then 1 else 1) else (if i = 39 then 1 else 1))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 1 else 1) else (if i = 41 then 1 else 1)) else (if i ≤ 42 then (if i = 42 then 1 else 1) else (if i ≤ 43 then (if i = 43 then 1 else 1) else (if i = 44 then 1 else 1)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 1 else 1) else (if i = 46 then 1 else 1)) else (if i ≤ 47 then (if i = 47 then 1 else 1) else (if i ≤ 48 then (if i = 48 then 1 else 1) else (if i = 49 then 1 else 1))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 1 else 1) else (if i = 51 then 1 else 1)) else (if i ≤ 52 then (if i = 52 then 1 else 1) else (if i ≤ 53 then (if i = 53 then 1 else 1) else (if i = 54 then 1 else 1)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 1 else 1) else (if i = 56 then 1 else 1)) else (if i ≤ 57 then (if i = 57 then 1 else 1) else (if i ≤ 58 then (if i = 58 then 1 else 1) else (if i = 59 then 1 else 1)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 1 else 1) else (if i = 61 then 1 else 1)) else (if i ≤ 62 then (if i = 62 then 1 else 1) else (if i ≤ 63 then (if i = 63 then 1 else 1) else (if i = 64 then 1 else 1)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1 else 1) else (if i = 66 then 1 else 1)) else (if i ≤ 67 then (if i = 67 then 1 else 1) else (if i ≤ 68 then (if i = 68 then 1 else 1) else (if i = 69 then 2 else 1))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2 else 1) else (if i = 71 then 2 else 1)) else (if i ≤ 72 then (if i = 72 then 2 else 1) else (if i ≤ 73 then (if i = 73 then 2 else 1) else (if i = 74 then 2 else 1)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2 else 1) else (if i = 76 then 2 else 1)) else (if i ≤ 77 then (if i = 77 then 2 else 1) else (if i ≤ 78 then (if i = 78 then 2 else 1) else (if i = 79 then 2 else 1)))))))) else 1

def LITN : ℕ → ℕ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 1637371946927 else 0) else (if i = 1 then 1688665241314 else 0)) else (if i ≤ 2 then (if i = 2 then 1739130035240 else 0) else (if i ≤ 3 then (if i = 3 then 1773031586916 else 0) else (if i = 4 then 1830778665144 else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 1881544463806 else 0) else (if i = 6 then 1908463260170 else 0)) else (if i ≤ 7 then (if i = 7 then 1948208802380 else 0) else (if i ≤ 8 then (if i = 8 then 1971446811027 else 0) else (if i = 9 then 2002522417684 else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 2016508659659 else 0) else (if i = 11 then 2037661517350 else 0)) else (if i ≤ 12 then (if i = 12 then 2066926388461 else 0) else (if i ≤ 13 then (if i = 13 then 2093835654991 else 0) else (if i = 14 then 2113349862345 else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 2131784738571 else 0) else (if i = 16 then 2148438545714 else 0)) else (if i ≤ 17 then (if i = 17 then 2163315904428 else 0) else (if i ≤ 18 then (if i = 18 then 2178151377246 else 0) else (if i = 19 then 2193604419174 else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 2208953458813 else 0) else (if i = 21 then 2225797864390 else 0)) else (if i ≤ 22 then (if i = 22 then 2241251080486 else 0) else (if i ≤ 23 then (if i = 23 then 2254535217783 else 0) else (if i = 24 then 2263405109651 else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 2273326306968 else 0) else (if i = 26 then 2286107258574 else 0)) else (if i ≤ 27 then (if i = 27 then 2297496408966 else 0) else (if i ≤ 28 then (if i = 28 then 2308335663490 else 0) else (if i = 29 then 2317080117574 else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 2326732223959 else 0) else (if i = 31 then 2335861391532 else 0)) else (if i ≤ 32 then (if i = 32 then 2344429179841 else 0) else (if i ≤ 33 then (if i = 33 then 2352609290688 else 0) else (if i = 34 then 2360419297239 else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 2367867686804 else 0) else (if i = 36 then 2374941456653 else 0)) else (if i ≤ 37 then (if i = 37 then 2381778368975 else 0) else (if i ≤ 38 then (if i = 38 then 2388599935368 else 0) else (if i = 39 then 2396130743452 else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 2402218617591 else 0) else (if i = 41 then 2408084970860 else 0)) else (if i ≤ 42 then (if i = 42 then 2412849470469 else 0) else (if i ≤ 43 then (if i = 43 then 2419232518842 else 0) else (if i = 44 then 2426171957503 else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 2432833536649 else 0) else (if i = 46 then 2439280699373 else 0)) else (if i ≤ 47 then (if i = 47 then 2445468172041 else 0) else (if i ≤ 48 then (if i = 48 then 2451456984940 else 0) else (if i = 49 then 2457201135336 else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 2462681152266 else 0) else (if i = 51 then 2466676946772 else 0)) else (if i ≤ 52 then (if i = 52 then 2471293499685 else 0) else (if i ≤ 53 then (if i = 53 then 2476641955536 else 0) else (if i = 54 then 2481487575389 else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 2486302147878 else 0) else (if i = 56 then 2490866118966 else 0)) else (if i ≤ 57 then (if i = 57 then 2494612157312 else 0) else (if i ≤ 58 then (if i = 58 then 2498678819804 else 0) else (if i = 59 then 2502878723481 else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 2506956427502 else 0) else (if i = 61 then 2510917076292 else 0)) else (if i ≤ 62 then (if i = 62 then 2515323479497 else 0) else (if i ≤ 63 then (if i = 63 then 2519109691421 else 0) else (if i = 64 then 2522794913424 else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 2526408444403 else 0) else (if i = 66 then 2529919227008 else 0)) else (if i ≤ 67 then (if i = 67 then 2533320796402 else 0) else (if i ≤ 68 then (if i = 68 then 2537079543429 else 0) else (if i = 69 then 2540330308375 else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 2543488928687 else 0) else (if i = 71 then 2546588549182 else 0)) else (if i ≤ 72 then (if i = 72 then 2549646740055 else 0) else (if i ≤ 73 then (if i = 73 then 2552622497165 else 0) else (if i = 74 then 2555498427509 else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 2558298585470 else 0) else (if i = 76 then 2561061054490 else 0)) else (if i ≤ 77 then (if i = 77 then 2563876493387 else 0) else (if i ≤ 78 then (if i = 78 then 2566556585717 else 0) else (if i = 79 then 2567874563535 else 0))))))))

def LIT0N : ℕ → ℕ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then 19722406717043 else 0) else (if i = 1 then 22666845696210 else 0)) else (if i ≤ 2 then (if i = 2 then 25802339912139 else 0) else (if i ≤ 3 then (if i = 3 then 29862782922685 else 0) else (if i = 4 then 33296770127170 else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then 39952210477538 else 0) else (if i = 6 then 47426982659936 else 0)) else (if i ≤ 7 then (if i = 7 then 51970277442206 else 0) else (if i ≤ 8 then (if i = 8 then 60018106799664 else 0) else (if i = 9 then 65738418576271 else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then 74205791072703 else 0) else (if i = 11 then 78496250513852 else 0)) else (if i ≤ 12 then (if i = 12 then 85263593639117 else 0) else (if i ≤ 13 then (if i = 13 then 95962830085874 else 0) else (if i = 14 then 107717610938680 else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then 117025168761372 else 0) else (if i = 16 then 126443904462313 else 0)) else (if i ≤ 17 then (if i = 17 then 136163288871973 else 0) else (if i ≤ 18 then (if i = 18 then 146017743730932 else 0) else (if i = 19 then 156732117054252 else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then 168828023209462 else 0) else (if i = 21 then 181932521960433 else 0)) else (if i ≤ 22 then (if i = 22 then 197570678225586 else 0) else (if i ≤ 23 then (if i = 23 then 213409876967954 else 0) else (if i = 24 then 228211958140725 else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then 239070630161760 else 0) else (if i = 26 then 251607570079691 else 0)) else (if i ≤ 27 then (if i = 27 then 268860043217769 else 0) else (if i ≤ 28 then (if i = 28 then 285629027450428 else 0) else (if i = 29 then 302536846523593 else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then 317079361096126 else 0) else (if i = 31 then 334324258972723 else 0)) else (if i ≤ 32 then (if i = 32 then 351795785058399 else 0) else (if i ≤ 33 then (if i = 33 then 369400647426023 else 0) else (if i = 34 then 387165123898804 else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then 405060674512290 else 0) else (if i = 36 then 423106222015562 else 0)) else (if i ≤ 37 then (if i = 37 then 441285700667350 else 0) else (if i ≤ 38 then (if i = 38 then 459570792738213 else 0) else (if i = 39 then 478659748406750 else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then 500533338214899 else 0) else (if i = 41 then 519162978608545 else 0)) else (if i ≤ 42 then (if i = 42 then 537910758130913 else 0) else (if i ≤ 43 then (if i = 43 then 553942613416667 else 0) else (if i = 44 then 576438846280327 else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then 601904296975317 else 0) else (if i = 46 then 627525047234963 else 0)) else (if i ≤ 47 then (if i = 47 then 653288356851015 else 0) else (if i ≤ 48 then (if i = 48 then 679199148533532 else 0) else (if i = 49 then 705248813835512 else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then 731481178430567 else 0) else (if i = 51 then 757883244575653 else 0)) else (if i ≤ 52 then (if i = 52 then 777768646838717 else 0) else (if i ≤ 53 then (if i = 53 then 801343163017871 else 0) else (if i = 54 then 830074517926343 else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then 856957709683647 else 0) else (if i = 56 then 884669237943364 else 0)) else (if i ≤ 57 then (if i = 57 then 911797972744585 else 0) else (if i ≤ 58 then (if i = 58 then 934810893571778 else 0) else (if i = 59 then 960657638711554 else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then 988123077672139 else 0) else (if i = 61 then 1015701638748621 else 0)) else (if i ≤ 62 then (if i = 62 then 1043394140124610 else 0) else (if i ≤ 63 then (if i = 63 then 1074935453792936 else 0) else (if i = 64 then 1102803247591794 else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then 1130786290413200 else 0) else (if i = 66 then 1158845454173611 else 0)) else (if i ≤ 67 then (if i = 67 then 1187031808819271 else 0) else (if i ≤ 68 then (if i = 68 then 1215334949815773 else 0) else (if i = 69 then 1247590065377182 else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then 1276070146495451 else 0) else (if i = 71 then 1304671278551722 else 0)) else (if i ≤ 72 then (if i = 72 then 1333334770608337 else 0) else (if i ≤ 73 then (if i = 73 then 1362053458356326 else 0) else (if i = 74 then 1390905236635801 else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then 1419890470873864 else 0) else (if i = 76 then 1448957759803987 else 0)) else (if i ≤ 77 then (if i = 77 then 1478081907995595 else 0) else (if i ≤ 78 then (if i = 78 then 1508381029107731 else 0) else (if i = 79 then 1537628512398329 else 0))))))))

def LIT1 : ℕ → ℚ := fun i => (if i ≤ 39 then (if i ≤ 19 then (if i ≤ 9 then (if i ≤ 4 then (if i ≤ 1 then (if i ≤ 0 then (if i = 0 then (2981753/1000000) else 0) else (if i = 1 then (3120901/1000000) else 0)) else (if i ≤ 2 then (if i = 2 then (3250463/1000000) else 0) else (if i ≤ 3 then (if i = 3 then (339661/100000) else 0) else (if i = 4 then (1752729/500000) else 0)))) else (if i ≤ 6 then (if i ≤ 5 then (if i = 5 then (1843841/500000) else 0) else (if i = 6 then (3859189/1000000) else 0)) else (if i ≤ 7 then (if i = 7 then (3950669/1000000) else 0) else (if i ≤ 8 then (if i = 8 then (1023661/250000) else 0) else (if i = 9 then (4185681/1000000) else 0))))) else (if i ≤ 14 then (if i ≤ 11 then (if i ≤ 10 then (if i = 10 then (107671/25000) else 0) else (if i = 11 then (545381/125000) else 0)) else (if i ≤ 12 then (if i = 12 then (889149/200000) else 0) else (if i ≤ 13 then (if i = 13 then (2281979/500000) else 0) else (if i = 14 then (4679511/1000000) else 0)))) else (if i ≤ 16 then (if i ≤ 15 then (if i = 15 then (4762387/1000000) else 0) else (if i = 16 then (1209949/250000) else 0)) else (if i ≤ 17 then (if i = 17 then (1228463/250000) else 0) else (if i ≤ 18 then (if i = 18 then (2491863/500000) else 0) else (if i = 19 then (631817/125000) else 0)))))) else (if i ≤ 29 then (if i ≤ 24 then (if i ≤ 21 then (if i ≤ 20 then (if i = 20 then (2564439/500000) else 0) else (if i = 21 then (5203633/1000000) else 0)) else (if i ≤ 22 then (if i = 22 then (2643047/500000) else 0) else (if i ≤ 23 then (if i = 23 then (1340803/250000) else 0) else (if i = 24 then (84848/15625) else 0)))) else (if i ≤ 26 then (if i ≤ 25 then (if i = 25 then (5476757/1000000) else 0) else (if i = 26 then (1381967/250000) else 0)) else (if i ≤ 27 then (if i = 27 then (1398547/250000) else 0) else (if i ≤ 28 then (if i = 28 then (5654691/1000000) else 0) else (if i = 29 then (5712201/1000000) else 0))))) else (if i ≤ 34 then (if i ≤ 31 then (if i ≤ 30 then (if i = 30 then (115183/20000) else 0) else (if i = 31 then (5812109/1000000) else 0)) else (if i ≤ 32 then (if i = 32 then (732881/125000) else 0) else (if i ≤ 33 then (if i = 33 then (5911879/1000000) else 0) else (if i = 34 then (5958849/1000000) else 0)))) else (if i ≤ 36 then (if i ≤ 35 then (if i = 35 then (3002017/500000) else 0) else (if i = 36 then (6047621/1000000) else 0)) else (if i ≤ 37 then (if i = 37 then (608969/100000) else 0) else (if i ≤ 38 then (if i = 38 then (613029/100000) else 0) else (if i = 39 then (1542747/250000) else 0))))))) else (if i ≤ 59 then (if i ≤ 49 then (if i ≤ 44 then (if i ≤ 41 then (if i ≤ 40 then (if i = 40 then (776959/125000) else 0) else (if i = 41 then (1250443/200000) else 0)) else (if i ≤ 42 then (if i = 42 then (628769/100000) else 0) else (if i ≤ 43 then (if i = 43 then (6317059/1000000) else 0) else (if i = 44 then (6356867/1000000) else 0)))) else (if i ≤ 46 then (if i ≤ 45 then (if i = 45 then (200003/31250) else 0) else (if i = 46 then (6441781/1000000) else 0)) else (if i ≤ 47 then (if i = 47 then (202563/31250) else 0) else (if i ≤ 48 then (if i = 48 then (407557/62500) else 0) else (if i = 49 then (1639637/250000) else 0))))) else (if i ≤ 54 then (if i ≤ 51 then (if i ≤ 50 then (if i = 50 then (6595069/1000000) else 0) else (if i = 51 then (6630527/1000000) else 0)) else (if i ≤ 52 then (if i = 52 then (6656427/1000000) else 0) else (if i ≤ 53 then (if i = 53 then (6686287/1000000) else 0) else (if i = 54 then (6721513/1000000) else 0)))) else (if i ≤ 56 then (if i ≤ 55 then (if i = 55 then (3376693/500000) else 0) else (if i = 56 then (6785211/1000000) else 0)) else (if i ≤ 57 then (if i = 57 then (851927/125000) else 0) else (if i ≤ 58 then (if i = 58 then (3420171/500000) else 0) else (if i = 59 then (214613/31250) else 0)))))) else (if i ≤ 69 then (if i ≤ 64 then (if i ≤ 61 then (if i ≤ 60 then (if i = 60 then (1379161/200000) else 0) else (if i = 61 then (1730833/250000) else 0)) else (if i ≤ 62 then (if i = 62 then (868779/125000) else 0) else (if i ≤ 63 then (if i = 63 then (6980013/1000000) else 0) else (if i = 64 then (875701/125000) else 0)))) else (if i ≤ 66 then (if i ≤ 65 then (if i = 65 then (3515333/500000) else 0) else (if i = 66 then (7055177/1000000) else 0)) else (if i ≤ 67 then (if i = 67 then (7079209/1000000) else 0) else (if i ≤ 68 then (if i = 68 then (1775693/250000) else 0) else (if i = 69 then (7128967/1000000) else 0))))) else (if i ≤ 74 then (if i ≤ 71 then (if i ≤ 70 then (if i = 70 then (3575769/500000) else 0) else (if i = 71 then (896713/125000) else 0)) else (if i ≤ 72 then (if i = 72 then (1798859/250000) else 0) else (if i ≤ 73 then (if i = 73 then (3608373/500000) else 0) else (if i = 74 then (1809427/250000) else 0)))) else (if i ≤ 76 then (if i ≤ 75 then (if i = 75 then (7258333/1000000) else 0) else (if i = 76 then (7278597/1000000) else 0)) else (if i ≤ 77 then (if i = 77 then (3649249/500000) else 0) else (if i ≤ 78 then (if i = 78 then (731879/100000) else 0) else (if i = 79 then (3668997/500000) else 0))))))))

def LIT0 : ℕ → ℚ := fun i => (LIT0N i : ℚ) / 1000000000000

def LsumB (i : ℕ) : ℕ :=
  (((List.range (blkB i + 1)).filter (fun p => isPrimeC p)).map (fun p => if p ≤ 47 then ubNon p (blkLp i p) else ubNon p 1)).sum

def RsumB (i : ℕ) : ℕ :=
  (((List.range (blkA i + 1)).filter (fun p => isPrimeC p)).map (fun p => if p ≤ 47 then blkMp i p * lbNon p else lbNon p)).sum

set_option maxHeartbeats 0 in
theorem chkL_all : (List.range 80).all (fun i => decide (LsumB i ≤ LITN i)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem chkR_all : (List.range 80).all (fun i => decide (LIT0N i ≤ RsumB i)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem chk1_all : (List.range 80).all (fun i => decide (LIT1 i ≤ logLower (LIT0 i))) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem chkM_all : (List.range 80).all (fun i => decide ((LITN i : ℚ)/1000000000000 ≤ (57711:ℚ)/100000 + logLower (LIT1 i))) = true := by decide +kernel

lemma rq_mono {p K K' : ℕ} (hp : 2 ≤ p) (h : K ≤ K') : rq p K ≤ rq p K' := by
  have hp0 : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 1 < p)
  have hden : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hpos : (0:ℚ) < (p:ℚ) ^ K := pow_pos hp0 K
  have hpos' : (0:ℚ) < (p:ℚ) ^ K' := pow_pos hp0 K'
  have hkey : (p:ℚ) ^ K ≤ (p:ℚ) ^ K' := pow_le_pow_right₀ (le_of_lt hp1) h
  have hpow : (p:ℚ) ^ (K+1) * (p:ℚ) ^ K' = (p:ℚ) ^ (K'+1) * (p:ℚ) ^ K := by
    rw [pow_succ, pow_succ]; ring
  unfold rq
  rw [div_le_div_iff₀ (mul_pos hpos hden) (mul_pos hpos' hden)]
  nlinarith [hkey, hden, hpos, hpow]

lemma rq_ge_one' {p j : ℕ} (hp : 2 ≤ p) (hj : 1 ≤ j) : (1:ℚ) ≤ rq p j := by
  have hp0 : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1:ℚ) ≤ (p:ℚ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hden : (0:ℚ) < (p:ℚ) - 1 := by
    have : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp
    linarith
  have hsplit : (p:ℚ)^(j+1) = (p:ℚ)^j * (p:ℚ) := by rw [pow_succ]
  have h : (1:ℚ) ≤ (p:ℚ)^j := one_le_pow₀ hp1
  have hpj : (0:ℚ) < (p:ℚ)^j := pow_pos hp0 j
  unfold rq
  rw [le_div_iff₀ (by positivity), hsplit]
  nlinarith [h, hpj]

lemma rq_le_two {p j : ℕ} (hp : 2 ≤ p) : rq p j ≤ 2 := by
  have hp0 : (0:ℚ) < (p:ℚ) := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp
  have hden : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hsplit : (p:ℚ)^(j+1) = (p:ℚ)^j * (p:ℚ) := by rw [pow_succ]
  have hpj : (0:ℚ) < (p:ℚ)^j := pow_pos hp0 j
  unfold rq
  rw [div_le_iff₀ (by positivity), hsplit]
  nlinarith [hpj, hp2]

lemma rq_lt_depth' {p j : ℕ} (hp : 2 ≤ p) : rq p j < 2 ^ logDepth := by
  calc rq p j ≤ 2 := rq_le_two hp
    _ < (2:ℚ)^logDepth := by norm_num [logDepth]

def smallPL : List ℕ := (List.range 48).filter (fun p => isPrimeC p)

lemma mem_smallPL {p : ℕ} (h47 : p ≤ 47) (hprime : Nat.Prime p) : p ∈ smallPL := by
  rw [smallPL, List.mem_filter, List.mem_range]
  exact ⟨by omega, (isPrimeC_iff p).mpr hprime⟩

lemma get2 {Q : ℕ → ℕ → Prop} [DecidableRel Q]
    (h : (List.range 80).all (fun i => smallPL.all (fun p => decide (Q i p))) = true)
    {i p : ℕ} (hi : i < 80) (hp : p ∈ smallPL) : Q i p := by
  have h1 := List.all_eq_true.mp h i (by rw [List.mem_range]; exact hi)
  have h2 := List.all_eq_true.mp h1 p hp
  rwa [decide_eq_true_eq] at h2

lemma getC {R : ℕ → Prop} [DecidablePred R]
    (h : (((List.range 1530).filter (fun p => isPrimeC p)).all (fun p => decide (R p))) = true)
    {p : ℕ} (hp : Nat.Prime p) (hlt : p < 1530) : R p := by
  have h1 := List.all_eq_true.mp h p (by
    rw [List.mem_filter, List.mem_range]
    exact ⟨hlt, (isPrimeC_iff p).mpr hp⟩)
  rwa [decide_eq_true_eq] at h1

lemma primesLT_triple : (((List.range 1530).filter (fun p => isPrimeC p)).all
    (fun p => decide (p ∈ plist))) = true := by decide +kernel

lemma plist_eq_plistB : plist = plistB := rfl

lemma mem_plistB_of {p : ℕ} (hp : Nat.Prime p) (h : p < 1530) : p ∈ plistB := by
  have h1 := getC primesLT_triple hp h
  rwa [plist_eq_plistB] at h1
set_option maxHeartbeats 0 in
theorem Kcap_ge_one : (((List.range 1530).filter (fun p => isPrimeC p)).all (fun p => decide (1 ≤ Kcap p))) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem kmaxC_blkLp_all : (List.range 80).all (fun i => smallPL.all (fun p => decide (kmaxC (blkNx i) p ≤ blkLp i p))) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem blkMp_kminC_all : (List.range 80).all (fun i => smallPL.all (fun p => decide (blkMp i p ≤ kminC (blkA i) p))) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem kmaxC_Lp_Kcap : (List.range 80).all (fun i => smallPL.all (fun p => decide (blkLp i p ≤ Kcap p))) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem ubF_bridge_all : (List.range 80).all (fun i => smallPL.all (fun p => decide (ubF p (blkLp i p) = (ubNon p (blkLp i p) : ℚ)/1000000000000))) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem ubF_bridge1_all : (((List.range 1530).filter (fun p => isPrimeC p)).all (fun p => decide (ubF p 1 = (ubNon p 1 : ℚ)/1000000000000))) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem lbF_bridge_all : (((List.range 1530).filter (fun p => isPrimeC p)).all (fun p => decide (lbF p = (lbNon p : ℚ)/1000000000000))) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem blk_mem_all : ((((List.range 1530).filter (fun p => isPrimeC p)).filter (fun xi => 17 ≤ xi)).all (fun xi => decide (blkA (blkIdx xi) ≤ xi ∧ xi ≤ blkB (blkIdx xi) ∧ nxF xi ≤ blkNx (blkIdx xi) ∧ blkNx (blkIdx xi) ≤ 1531 ∧ xi ≤ 1523 ∧ blkIdx xi < 80))) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem nxf_prime_all : ((((List.range 1530).filter (fun p => isPrimeC p)).filter (fun xi => 17 ≤ xi)).all (fun xi => isPrimeC (nxF xi))) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem nxf_gt_all : ((((List.range 1530).filter (fun p => isPrimeC p)).filter (fun xi => 17 ≤ xi)).all (fun xi => decide (xi < nxF xi))) = true := by decide +kernel

def pfS (ξ : ℕ) : Finset ℕ := (Finset.range (ξ + 1)).filter Nat.Prime

lemma pfS_subset_pfS {a b : ℕ} (h : a ≤ b) : pfS a ⊆ pfS b := by
  intro p hp
  simp only [pfS, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

lemma pfS_subset_cL {b : ℕ} : pfS b ⊆ (((List.range (b + 1)).filter (fun p => isPrimeC p)).toFinset) := by
  intro p hp
  simp only [pfS, Finset.mem_filter, Finset.mem_range] at hp
  have hpp : Nat.Prime p := hp.2
  have hp_le : p ≤ b := by omega
  rw [List.mem_toFinset, List.mem_filter, List.mem_range]
  exact ⟨by omega, (isPrimeC_iff p).mpr hpp⟩

lemma cL_subset_pfS {a : ℕ} : (((List.range (a + 1)).filter (fun p => isPrimeC p)).toFinset) ⊆ pfS a := by
  intro p hp
  rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hp
  obtain ⟨hle, hic⟩ := hp
  have hpp : Nat.Prime p := (isPrimeC_iff p).mp hic
  simp only [pfS, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpp⟩

lemma sum_cL_eq (b : ℕ) (f : ℕ → ℕ) :
    (((List.range (b + 1)).filter (fun p => isPrimeC p)).map f).sum
      = (((List.range (b + 1)).filter (fun p => isPrimeC p)).toFinset).sum f :=
  (List.sum_toFinset f ((List.Nodup.filter _ List.nodup_range))).symm

lemma LsumB_eq (i : ℕ) :
    LsumB i = (((List.range (blkB i + 1)).filter (fun p => isPrimeC p)).toFinset).sum
      (fun p => if p ≤ 47 then ubNon p (blkLp i p) else ubNon p 1) :=
  sum_cL_eq (blkB i) (fun p => if p ≤ 47 then ubNon p (blkLp i p) else ubNon p 1)

lemma RsumB_eq (i : ℕ) :
    RsumB i = (((List.range (blkA i + 1)).filter (fun p => isPrimeC p)).toFinset).sum
      (fun p => if p ≤ 47 then blkMp i p * lbNon p else lbNon p) :=
  sum_cL_eq (blkA i) (fun p => if p ≤ 47 then blkMp i p * lbNon p else lbNon p)

set_option maxHeartbeats 1000000

-- ================= copies of useful private lemmas (from robin_Neps_of_margin) =====
lemma log_sigma_pow_sub_log_pow {p a : ℕ} (hp : Nat.Prime p) :
    Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) - Real.log ((p ^ a : ℕ) : ℝ) =
      Real.log ((((p : ℝ) ^ (a + 1 : ℕ)) - 1) / (((p : ℝ) ^ a) * ((p : ℝ) - 1))) := by
  have hpa : 0 < p ^ a := pow_pos (Nat.Prime.pos hp) a
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ a) := (ArithmeticFunction.sigma_pos_iff).2 hpa
  have hσr : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) := by exact_mod_cast hσ
  have hpar : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) := by exact_mod_cast hpa
  have hclosed : ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) =
      (((p : ℝ) ^ (a + 1 : ℕ)) - 1) / (((p : ℝ) ^ a) * ((p : ℝ) - 1)) := by
    simpa using (sigma_one_ratio_prime_pow (p := p) (k := a) hp)
  calc Real.log (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) - Real.log ((p ^ a : ℕ) : ℝ)
      = Real.log ((((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ)) / ((p ^ a : ℕ) : ℝ)) := by
          rw [← Real.log_div hσr.ne' hpar.ne']
    _ = _ := by rw [hclosed]

lemma sigma_prod_prime_pows {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p) (a : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
      have hp' : Nat.Prime p := hprime p (by simp)
      have hcop : (p ^ a p).Coprime (Finset.prod s (fun q => q ^ a q)) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq' : Nat.Prime q := hprime q (Finset.mem_insert_of_mem hq)
        have hpq_ne : q ≠ p := by
          intro hpq; exact hpnot (by simpa [hpq] using hq)
        have hpq : p.Coprime q := (Nat.coprime_primes hp' hq').mpr (Ne.symm hpq_ne)
        have h1 : p.Coprime (q ^ a q) := Nat.Coprime.pow_right (a q) hpq
        exact Nat.Coprime.pow_left (a p) h1
      have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have ih' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpnot, hσ, ih', Finset.prod_insert hpnot]


set_option maxHeartbeats 1000000

-- muF antitone in eps
lemma muF_antitone {p : ℕ} (hp : 2 ≤ p) {ε₁ ε₂ : ℝ} (h0 : 0 < ε₁) (hle : ε₁ ≤ ε₂) :
    muF p ε₂ ≤ muF p ε₁ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hq₁ : (p:ℝ) < (p:ℝ)^(1+ε₁) := by
    calc (p:ℝ) = (p:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ < (p:ℝ)^(1+ε₁) := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hmono : (p:ℝ) ^ (1 + ε₁) ≤ (p:ℝ) ^ (1 + ε₂) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) (by linarith : (1:ℝ) + ε₁ ≤ 1 + ε₂)
  have hq₂ : (p:ℝ) < (p:ℝ)^(1+ε₂) := lt_of_lt_of_le hq₁ hmono
  have hnum1 : (1:ℝ) ≤ ((p:ℝ)^(1+ε₁) - 1)/((p:ℝ)^(1+ε₁) - (p:ℝ)) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hnum2 : (1:ℝ) ≤ ((p:ℝ)^(1+ε₂) - 1)/((p:ℝ)^(1+ε₂) - (p:ℝ)) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  unfold muF
  apply div_le_div_of_nonneg_right _ (le_of_lt hlogp)
  apply Real.log_le_log (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hmono, hp0]

lemma thrSet_mono {ξ₁ ξ₂ p : ℕ} (h : ξ₁ ≤ ξ₂) : thrSet ξ₁ p ⊆ thrSet ξ₂ p := by
  intro j hj
  simp only [thrSet, Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans hj.2 h⟩

lemma kminC_mono {ξ₁ ξ₂ p : ℕ} (h : ξ₁ ≤ ξ₂) : kminC ξ₁ p ≤ kminC ξ₂ p := by
  by_cases hne : (thrSet ξ₁ p).Nonempty
  · have hne2 : (thrSet ξ₂ p).Nonempty := hne.mono (thrSet_mono h)
    have hk1 : kminC ξ₁ p = (thrSet ξ₁ p).max' hne := by rw [kminC, dif_pos hne]
    have hk2 : kminC ξ₂ p = (thrSet ξ₂ p).max' hne2 := by rw [kminC, dif_pos hne2]
    rw [hk1, hk2]
    apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (thrSet_mono h hx)
  · have hk1 : kminC ξ₁ p = 1 := by rw [kminC, dif_neg hne]
    rw [hk1]
    exact one_le_kminC ξ₂ p

lemma kmaxC_mono {ξ₁ ξ₂ p : ℕ} (h : ξ₁ ≤ ξ₂) : kmaxC ξ₁ p ≤ kmaxC ξ₂ p := kminC_mono h

lemma kminC_le_floor {ξ p : ℕ} (hξ : 2 ≤ ξ) (hp : Nat.Prime p) (hpξ : p ≤ ξ) :
    kminC ξ p ≤ ⌊muF p (Fq ξ 1)⌋₊ :=
  Nat.le_floor (kminC_le ξ p hξ hp hpξ)

lemma muF_nonneg {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) : 0 ≤ muF p ε :=
  le_of_lt (Commons.NumberTheory.Robin.caMu_pos hp hε)

-- a_p ≥ kminC ξ p   (eps ≤ Fq ξ 1)
lemma a_ge_kminC {ξ p : ℕ} {ε : ℝ} (hξ : 2 ≤ ξ) (hp : Nat.Prime p) (hpξ : p ≤ ξ)
    (hε : 0 < ε) (hle : ε ≤ Fq ξ 1) :
    kminC ξ p ≤ ⌊muF p ε⌋₊ := by
  have hξ2 : 2 ≤ ξ := hξ
  have hmono : muF p (Fq ξ 1) ≤ muF p ε := muF_antitone hp.two_le hε hle
  calc kminC ξ p ≤ ⌊muF p (Fq ξ 1)⌋₊ := kminC_le_floor hξ hp hpξ
    _ ≤ ⌊muF p ε⌋₊ := Nat.floor_le_floor hmono

-- a_p ≤ kmaxC ξnext p   (Fq ξnext 1 ≤ eps)
lemma a_le_kmaxC {ξnext p : ℕ} {ε : ℝ} (hξnext : Nat.Prime ξnext) (hp : Nat.Prime p)
    (hgt : p < ξnext) (hle1531 : ξnext ≤ 1531) (hε : 0 < ε) (hge : Fq ξnext 1 ≤ ε) :
    ⌊muF p ε⌋₊ ≤ kmaxC ξnext p := by
  have hmono : muF p ε ≤ muF p (Fq ξnext 1) := muF_antitone hp.two_le (Fq_pos ξnext hξnext.two_le) hge
  calc ⌊muF p ε⌋₊ ≤ ⌊muF p (Fq ξnext 1)⌋₊ := Nat.floor_le_floor hmono
    _ ≤ kmaxC ξnext p := kmaxC_ge ξnext p hξnext hp hgt hle1531


lemma blk_mem' {ξ : ℕ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523) :
    ξ ∈ ((List.range 1530).filter (fun p => isPrimeC p)).filter (fun xi => 17 ≤ xi) := by
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_filter, List.mem_range]
    exact ⟨by omega, (isPrimeC_iff ξ).mpr hξp⟩
  · rw [decide_eq_true_eq]; exact h17

lemma blk_facts {ξ : ℕ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523) :
    blkA (blkIdx ξ) ≤ ξ ∧ ξ ≤ blkB (blkIdx ξ) ∧ nxF ξ ≤ blkNx (blkIdx ξ) ∧ blkNx (blkIdx ξ) ≤ 1531 ∧ ξ ≤ 1523 ∧ blkIdx ξ < 80 := by
  have h := List.all_eq_true.mp blk_mem_all ξ (blk_mem' hξp h17 h1523)
  simpa [decide_eq_true_eq] using h

lemma nxF_prime {ξ : ℕ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523) : Nat.Prime (nxF ξ) := by
  have h := List.all_eq_true.mp nxf_prime_all ξ (blk_mem' hξp h17 h1523)
  exact (isPrimeC_iff (nxF ξ)).mp h

lemma nxF_gt {ξ : ℕ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523) : ξ < nxF ξ := by
  have h := List.all_eq_true.mp nxf_gt_all ξ (blk_mem' hξp h17 h1523)
  simpa using h

-- pointwise LHS bound
lemma per_term_le {ξ p : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523)
    (hε : 0 < ε) (hεgt : Fq (nxF ξ) 1 < ε)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ ξ → 1 ≤ ⌊muF q ε⌋₊)
    (hp : p ∈ pfS ξ) :
    Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ)) ≤
      (if p ≤ 47 then (ubNon p (blkLp (blkIdx ξ) p) : ℝ) else (ubNon p 1 : ℝ)) / 1000000000000 := by
  obtain ⟨ha_le, hb_ge, hnx_le, hnx1531, h1523', hblk80⟩ := blk_facts hξp h17 h1523
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp1530 : p < 1530 := by
    have h := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_range] at h
    omega
  have hple : p ≤ ξ := by
    have h := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_range] at h
    omega
  have ha1 : 1 ≤ ⌊muF p ε⌋₊ := hsupp p hprime hple
  have hp2 : 2 ≤ p := hprime.two_le
  have hp47 : p ≤ 47 ∨ 53 ≤ p := by
    rcases Nat.lt_or_ge p 48 with h | h
    · left; omega
    · right
      by_contra hcon
      push_neg at hcon
      interval_cases p <;> revert hprime <;> decide
  rcases hp47 with hp47 | hp53
  · -- p ≤ 47
    have hnxFp : Nat.Prime (nxF ξ) := nxF_prime hξp h17 h1523
    have hlt : p < nxF ξ := lt_of_le_of_lt hple (nxF_gt hξp h17 h1523)
    have hFq : Fq (nxF ξ) 1 ≤ ε := le_of_lt hεgt
    have haL : ⌊muF p ε⌋₊ ≤ blkLp (blkIdx ξ) p := by
      have h1 : ⌊muF p ε⌋₊ ≤ kmaxC (nxF ξ) p := a_le_kmaxC hnxFp hprime hlt (by omega) hε hFq
      have h2 : kmaxC (nxF ξ) p ≤ kmaxC (blkNx (blkIdx ξ)) p := kmaxC_mono hnx_le
      have h3 : kmaxC (blkNx (blkIdx ξ)) p ≤ blkLp (blkIdx ξ) p :=
        get2 kmaxC_blkLp_all (by omega) (mem_smallPL hp47 hprime)
      linarith
    have hK1 : 1 ≤ blkLp (blkIdx ξ) p := by
      have h := get2 kmaxC_blkLp_all (by omega) (mem_smallPL hp47 hprime)
      have := one_le_kmaxC (blkNx (blkIdx ξ)) p
      omega
    have hKcap : blkLp (blkIdx ξ) p ≤ Kcap p :=
      get2 kmaxC_Lp_Kcap (by omega) (mem_smallPL hp47 hprime)
    have hge1 : (1:ℚ) ≤ rq p (blkLp (blkIdx ξ) p) := rq_ge_one' hp2 hK1
    have hlt2 : rq p (blkLp (blkIdx ξ) p) < 2 ^ logDepth := rq_lt_depth' hp2
    have hub : Real.log (((rq p (blkLp (blkIdx ξ) p) : ℚ) : ℝ)) ≤ (ubNon p (blkLp (blkIdx ξ) p) : ℝ)/1000000000000 := by
      have hU := logUpper_ge_log (rq p (blkLp (blkIdx ξ) p)) (by exact_mod_cast hge1) hlt2
      have hL := ubLeafAll p (blkLp (blkIdx ξ) p) hK1 hKcap (mem_plistB_of hprime hp1530)
      have hbr : ubF p (blkLp (blkIdx ξ) p) = (ubNon p (blkLp (blkIdx ξ) p) : ℚ)/1000000000000 :=
        get2 ubF_bridge_all (by omega) (mem_smallPL hp47 hprime)
      calc Real.log (((rq p (blkLp (blkIdx ξ) p) : ℚ) : ℝ))
          ≤ ((ubF p (blkLp (blkIdx ξ) p) : ℚ) : ℝ) := hU.trans (by exact_mod_cast hL)
        _ = (ubNon p (blkLp (blkIdx ξ) p) : ℝ)/1000000000000 := by rw [hbr]; push_cast; ring
    have hmono : Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ)) ≤ Real.log (((rq p (blkLp (blkIdx ξ) p) : ℚ) : ℝ)) := by
      apply Real.log_le_log
      · have : (0:ℚ) < rq p (⌊muF p ε⌋₊) := by
          have := rq_ge_one' hp2 ha1; linarith
        exact_mod_cast this
      · exact_mod_cast rq_mono hp2 haL
    rw [if_pos hp47]
    exact hmono.trans hub
  · -- 53 ≤ p
    have hnxFp : Nat.Prime (nxF ξ) := nxF_prime hξp h17 h1523
    have h1531lt : Fq 1531 1 < ε := by
      have h1 : Fq 1531 1 ≤ Fq (nxF ξ) 1 := Fq_mono hnxFp.two_le (by norm_num) (le_trans hnx_le hnx1531)
      linarith
    have ha_eq : ⌊muF p ε⌋₊ = 1 := by
      have hle1 : ¬ (ε ≤ Fq p 2) := by
        have h53 : Fq p 2 ≤ Fq 53 2 := Fq2_le (by norm_num : 2 ≤ 53) hp2 hp53
        have hb : Fq 53 2 < Fq 1531 1 := F53b
        linarith
      have hlt2 : ⌊muF p ε⌋₊ < 2 := by
        by_contra hcon
        push_neg at hcon
        have h2 : (2:ℝ) ≤ muF p ε := (Nat.le_floor_iff (muF_nonneg hp2 hε)).mp hcon
        exact hle1 ((Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε 2 hp2 hε (by norm_num)).mp (by simpa [muF] using h2))
      omega
    have hK1 : 1 = 1 := rfl
    have hge1 : (1:ℚ) ≤ rq p 1 := rq_ge_one' hp2 (le_refl 1)
    have hlt2 : rq p 1 < 2 ^ logDepth := rq_lt_depth' hp2
    have hbr : ubF p 1 = (ubNon p 1 : ℚ)/1000000000000 := getC ubF_bridge1_all hprime hp1530
    have hub : Real.log (((rq p 1 : ℚ) : ℝ)) ≤ (ubNon p 1 : ℝ)/1000000000000 := by
      have hU := logUpper_ge_log (rq p 1) (by exact_mod_cast hge1) hlt2
      have hL := ubLeafAll p 1 (le_refl 1) (getC Kcap_ge_one hprime hp1530) (mem_plistB_of hprime hp1530)
      calc Real.log (((rq p 1 : ℚ) : ℝ)) ≤ ((ubF p 1 : ℚ) : ℝ) := hU.trans (by exact_mod_cast hL)
        _ = (ubNon p 1 : ℝ)/1000000000000 := by rw [hbr]; push_cast; ring
    rw [if_neg (by omega : ¬ p ≤ 47)]
    simpa [ha_eq] using hub

lemma log_ratio_eq {M ξ : ℕ} {ε : ℝ} (hM : M = ∏ p ∈ pfS ξ, p ^ (⌊muF p ε⌋₊)) :
    Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ) : ℝ)
      = ∑ p ∈ pfS ξ, Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ)) := by
  have hfac : ArithmeticFunction.sigma 1 M
      = ∏ p ∈ pfS ξ, ArithmeticFunction.sigma 1 (p ^ ⌊muF p ε⌋₊) := by
    rw [hM]
    exact sigma_prod_prime_pows (fun p hp => (Finset.mem_filter.mp hp).2) _
  have hlogσ : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ))
      = ∑ p ∈ pfS ξ, Real.log (((ArithmeticFunction.sigma 1 (p ^ ⌊muF p ε⌋₊) : ℕ) : ℝ)) := by
    rw [hfac, Nat.cast_prod, Real.log_prod]
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ ⌊muF p ε⌋₊) :=
      (ArithmeticFunction.sigma_pos_iff).2 (pow_pos hprime.pos _)
    exact_mod_cast (ne_of_gt hσ)
  have hlogM : Real.log ((M:ℕ) : ℝ)
      = ∑ p ∈ pfS ξ, ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) := by
    rw [hM, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hpos : 0 < p ^ ⌊muF p ε⌋₊ := pow_pos hprime.pos _
      have : (0:ℝ) < (((p ^ ⌊muF p ε⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hpos
      exact ne_of_gt this
  rw [hlogσ, hlogM, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have h := log_sigma_pow_sub_log_pow (p := p) (a := ⌊muF p ε⌋₊) hprime
  have h2 : Real.log (((p ^ ⌊muF p ε⌋₊ : ℕ)) : ℝ) = ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [← h2]
  simpa [rq] using h

lemma chainL {M ξ : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523)
    (hε : 0 < ε) (hεgt : Fq (nxF ξ) 1 < ε)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ ξ → 1 ≤ ⌊muF q ε⌋₊)
    (hM : M = ∏ p ∈ pfS ξ, p ^ (⌊muF p ε⌋₊)) :
    Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ)
      ≤ (LsumB (blkIdx ξ) : ℝ)/1000000000000 := by
  obtain ⟨ha_le, hb_ge, hnx_le, hnx1531, h1523', hblk80⟩ := blk_facts hξp h17 h1523
  rw [log_ratio_eq hM]
  have hset : pfS (blkB (blkIdx ξ)) = (((List.range (blkB (blkIdx ξ) + 1)).filter (fun p => isPrimeC p)).toFinset) :=
    Finset.Subset.antisymm pfS_subset_cL cL_subset_pfS
  have h1 : ∑ p ∈ pfS ξ, Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ))
      ≤ ∑ p ∈ pfS (blkB (blkIdx ξ)),
          ((if p ≤ 47 then ubNon p (blkLp (blkIdx ξ) p) else ubNon p 1) : ℝ)/1000000000000 := by
    apply le_trans (Finset.sum_le_sum (fun p hp => per_term_le hξp h17 h1523 hε hεgt hsupp hp))
    apply Finset.sum_le_sum_of_subset_of_nonneg (pfS_subset_pfS hb_ge)
    intro p hp _
    split_ifs <;> positivity
  refine h1.trans ?_
  rw [hset, LsumB_eq, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs <;> exact le_of_eq (by ring)

-- ==================== chainR : lower bound for log M ====================
lemma chainR {M ξ : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523)
    (hε : 0 < ε) (hεle : ε ≤ Fq ξ 1)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ ξ → 1 ≤ ⌊muF q ε⌋₊)
    (hM : M = ∏ p ∈ pfS ξ, p ^ ⌊muF p ε⌋₊) :
    (RsumB (blkIdx ξ) : ℝ)/1000000000000 ≤ Real.log ((M:ℕ):ℝ) := by
  obtain ⟨ha_le, hb_ge, hnx_le, hnx1531, hξ1523, hblk80⟩ := blk_facts hξp h17 h1523
  have hlogM : Real.log ((M:ℕ):ℝ) = ∑ p ∈ pfS ξ, ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) := by
    rw [hM, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hpos : (0:ℝ) < ((p ^ ⌊muF p ε⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (pow_pos hprime.pos _)
      exact ne_of_gt hpos
  have hsetA : pfS (blkA (blkIdx ξ)) =
      (((List.range (blkA (blkIdx ξ) + 1)).filter (fun p => isPrimeC p)).toFinset) :=
    Finset.Subset.antisymm pfS_subset_cL cL_subset_pfS
  have hbound : (RsumB (blkIdx ξ) : ℝ)/1000000000000 ≤
      ∑ p ∈ pfS (blkA (blkIdx ξ)), ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) := by
    rw [RsumB_eq, hsetA, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hpS : p ∈ pfS (blkA (blkIdx ξ)) := cL_subset_pfS hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    have hpA : p ≤ blkA (blkIdx ξ) := by
      have h := (Finset.mem_filter.mp hpS).1
      simp only [Finset.mem_range] at h
      omega
    have hpξ : p ≤ ξ := le_trans hpA ha_le
    have ha1 : (1:ℝ) ≤ ((⌊muF p ε⌋₊ : ℕ) : ℝ) := by
      have := hsupp p hpprime hpξ
      exact_mod_cast this
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    have hbridge : ((lbF p : ℚ) : ℝ) = (lbNon p : ℝ)/1000000000000 := by
      have h := getC lbF_bridge_all hpprime (by omega : p < 1530)
      rw [h]; push_cast; ring
    have hlb : ((lbF p : ℚ) : ℝ) ≤ Real.log (p:ℝ) := by
      have hm : p ∈ plistB := mem_plistB_of hpprime (by omega : p < 1530)
      have h1 : lbF p ≤ logLower (p:ℚ) := lbLeafAll p hm
      have h1' : ((lbF p : ℚ) : ℝ) ≤ ((logLower (p:ℚ) : ℚ) : ℝ) := by exact_mod_cast h1
      have hD : (2:ℚ) ^ logDepth = 8192 := by norm_num [logDepth]
      have h2 : ((logLower (p:ℚ) : ℚ) : ℝ) ≤ Real.log (p:ℝ) := by
        have := logLower_le_log (p:ℚ) (by exact_mod_cast hpprime.one_le) (by rw [hD]; exact_mod_cast (by omega : p < 8192))
        simpa using this
      exact h1'.trans h2
    split_ifs with h47
    · have hKm : (blkMp (blkIdx ξ) p : ℕ) ≤ ⌊muF p ε⌋₊ := by
        have h1 := get2 blkMp_kminC_all hblk80 (mem_smallPL h47 hpprime)
        have h2 : kminC (blkA (blkIdx ξ)) p ≤ kminC ξ p := kminC_mono ha_le
        have h3 : kminC ξ p ≤ ⌊muF p ε⌋₊ := a_ge_kminC hξp.two_le hpprime hpξ hε hεle
        omega
      have hKm' : ((blkMp (blkIdx ξ) p : ℕ) : ℝ) ≤ ((⌊muF p ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast hKm
      have heq : ((blkMp (blkIdx ξ) p * lbNon p : ℕ) : ℝ) / 1000000000000
          = ((blkMp (blkIdx ξ) p : ℕ) : ℝ) * ((lbF p : ℚ) : ℝ) := by
        push_cast
        rw [hbridge]
        ring
      rw [heq]
      exact mul_le_mul hKm' hlb (by rw [hbridge]; positivity) (by positivity)
    · have h2 : (lbNon p : ℝ)/1000000000000 ≤ Real.log (p:ℝ) := by
        rw [← hbridge]; exact hlb
      have h1 : Real.log (p:ℝ) ≤ ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) :=
        le_mul_of_one_le_left hlogp ha1
      exact h2.trans h1
  refine hbound.trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (pfS_subset_pfS ha_le) (fun p hp _ => by positivity)).trans ?_
  exact le_of_eq hlogM.symm

-- ==================== extraction of the numeric checks ====================
lemma get80 {R : ℕ → Prop} [DecidablePred R]
    (h : (List.range 80).all (fun i => decide (R i)) = true) {i : ℕ} (hi : i < 80) : R i := by
  have h1 := List.all_eq_true.mp h i (by rw [List.mem_range]; exact hi)
  rwa [decide_eq_true_eq] at h1

lemma LsumB_le_LITN_R (i : ℕ) (hi : i < 80) :
    (LsumB i : ℝ)/1000000000000 ≤ (LITN i : ℝ)/1000000000000 := by
  have h := get80 chkL_all hi
  have h' : (LsumB i : ℝ) ≤ (LITN i : ℝ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right h' (by norm_num)

lemma LIT0N_le_RsumB_R (i : ℕ) (hi : i < 80) :
    (LIT0N i : ℝ)/1000000000000 ≤ (RsumB i : ℝ)/1000000000000 := by
  have h := get80 chkR_all hi
  have h' : (LIT0N i : ℝ) ≤ (RsumB i : ℝ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right h' (by norm_num)

lemma LIT1_le_logLower_R (i : ℕ) (hi : i < 80) :
    (LIT1 i : ℝ) ≤ ((logLower (LIT0 i) : ℚ) : ℝ) := by
  have h := get80 chk1_all hi
  exact_mod_cast h

lemma LITN_le_chkM_R (i : ℕ) (hi : i < 80) :
    (LITN i : ℝ)/1000000000000 ≤ (57711:ℝ)/100000 + ((logLower (LIT1 i) : ℚ) : ℝ) := by
  have h := get80 chkM_all hi
  have h' : (((LITN i : ℚ)/1000000000000 : ℚ) : ℝ) ≤
      (((57711:ℚ)/100000 + logLower (LIT1 i) : ℚ) : ℝ) := by exact_mod_cast h
  simpa using h'

theorem chkP_all : (List.range 80).all (fun i => decide ((1:ℚ) < LIT1 i ∧ LIT1 i < 2 ^ logDepth
    ∧ (1:ℚ) < LIT0 i ∧ LIT0 i < 2 ^ logDepth)) = true := by decide +kernel

lemma LIT1_gt_one_q (i : ℕ) (hi : i < 80) : (1:ℚ) < LIT1 i := (get80 chkP_all hi).1

lemma LIT1_lt_depth_q (i : ℕ) (hi : i < 80) : LIT1 i < (2:ℚ) ^ logDepth := (get80 chkP_all hi).2.1

lemma LIT0_gt_one_q (i : ℕ) (hi : i < 80) : (1:ℚ) < LIT0 i := (get80 chkP_all hi).2.2.1

lemma LIT0_lt_depth_q (i : ℕ) (hi : i < 80) : LIT0 i < (2:ℚ) ^ logDepth := (get80 chkP_all hi).2.2.2

lemma LIT1_gt_one (i : ℕ) (hi : i < 80) : (1:ℝ) < (LIT1 i : ℝ) := by
  have h := LIT1_gt_one_q i hi; exact_mod_cast h

lemma LIT0_gt_one (i : ℕ) (hi : i < 80) : (1:ℝ) < (LIT0 i : ℝ) := by
  have h := LIT0_gt_one_q i hi; exact_mod_cast h

-- ==================== main bound for the block range 17 ≤ ξ ≤ 1523 ====================
lemma robin_bound_block {M ξ : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (h17 : 17 ≤ ξ) (h1523 : ξ ≤ 1523)
    (hε : 0 < ε) (hεgt : Fq (nxF ξ) 1 < ε)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ ξ → 1 ≤ ⌊muF q ε⌋₊)
    (hεle : ε ≤ Fq ξ 1)
    (hM : M = ∏ p ∈ pfS ξ, p ^ ⌊muF p ε⌋₊) :
    ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ)) := by
  obtain ⟨ha_le, hb_ge, hnx_le, hnx1531, hξ1523, hblk80⟩ := blk_facts hξp h17 h1523
  have hL := chainL hξp h17 h1523 hε hεgt hsupp hM
  have hR := chainR hξp h17 h1523 hε hεle hsupp hM
  have hMpos : (0:ℝ) < (M:ℝ) := by
    have h : 0 < M := by
      rw [hM]
      exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    exact_mod_cast h
  have hσpos : (0:ℝ) < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) := by
    have h : 0 < M := by
      rw [hM]
      exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    have := (ArithmeticFunction.sigma_pos_iff (k := 1)).2 h
    exact_mod_cast this
  have hLT0 : (LIT0 (blkIdx ξ) : ℝ) ≤ Real.log ((M:ℕ):ℝ) := by
    have h2 : (LIT0N (blkIdx ξ) : ℝ)/1000000000000 ≤ (RsumB (blkIdx ξ) : ℝ)/1000000000000 :=
      LIT0N_le_RsumB_R (blkIdx ξ) hblk80
    have h3 : ((LIT0 (blkIdx ξ) : ℚ) : ℝ) = (LIT0N (blkIdx ξ) : ℝ)/1000000000000 := by
      simp [LIT0]
    rw [h3]
    exact h2.trans hR
  have hll : ((logLower (LIT1 (blkIdx ξ)) : ℚ) : ℝ) ≤ Real.log (LIT1 (blkIdx ξ) : ℝ) := by
    apply logLower_le_log
    · exact le_of_lt (LIT1_gt_one_q (blkIdx ξ) hblk80)
    · exact LIT1_lt_depth_q (blkIdx ξ) hblk80
  have hLT1 : (LIT1 (blkIdx ξ) : ℝ) ≤ Real.log (LIT0 (blkIdx ξ) : ℝ) := by
    have h1 : (LIT1 (blkIdx ξ) : ℝ) ≤ ((logLower (LIT0 (blkIdx ξ)) : ℚ) : ℝ) :=
      LIT1_le_logLower_R (blkIdx ξ) hblk80
    have h2 : ((logLower (LIT0 (blkIdx ξ)) : ℚ) : ℝ) ≤ Real.log (LIT0 (blkIdx ξ) : ℝ) := by
      apply logLower_le_log
      · exact le_of_lt (LIT0_gt_one_q (blkIdx ξ) hblk80)
      · exact LIT0_lt_depth_q (blkIdx ξ) hblk80
    exact h1.trans h2
  have hlogchain : ((logLower (LIT1 (blkIdx ξ)) : ℚ) : ℝ) ≤
      Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    have h1 : (0:ℝ) < (LIT1 (blkIdx ξ) : ℝ) := by linarith [LIT1_gt_one (blkIdx ξ) hblk80]
    calc ((logLower (LIT1 (blkIdx ξ)) : ℚ) : ℝ) ≤ Real.log (LIT1 (blkIdx ξ) : ℝ) := hll
      _ ≤ Real.log (Real.log (LIT0 (blkIdx ξ) : ℝ)) := Real.log_le_log h1 hLT1
      _ ≤ Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
          apply Real.log_le_log (Real.log_pos (LIT0_gt_one (blkIdx ξ) hblk80))
          exact Real.log_le_log (by linarith [LIT0_gt_one (blkIdx ξ) hblk80]) hLT0
  have hstep2 : (57711:ℝ)/100000 + ((logLower (LIT1 (blkIdx ξ)) : ℚ) : ℝ) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    have hγ : (57711:ℝ)/100000 ≤ Real.eulerMascheroniConstant := by
      have h := gammaLo_le
      rw [Rat.cast_div] at h
      norm_num at h
      exact h
    linarith
  have hfinal : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    refine hL.trans (le_trans ?_ hstep2)
    exact (LsumB_le_LITN_R (blkIdx ξ) hblk80).trans (LITN_le_chkM_R (blkIdx ξ) hblk80)
  have hlogM1 : (1:ℝ) < Real.log ((M:ℕ):ℝ) :=
    lt_of_lt_of_le (LIT0_gt_one (blkIdx ξ) hblk80) hLT0
  have hlogσ : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) ≤
      Real.log ((M:ℕ):ℝ) + Real.eulerMascheroniConstant +
        Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by linarith
  have hexp := Real.exp_le_exp.mpr hlogσ
  rw [Real.exp_log hσpos] at hexp
  have hllpos : 0 < Real.log (Real.log ((M:ℕ):ℝ)) := Real.log_pos hlogM1
  have hrhs : Real.exp (Real.log ((M:ℕ):ℝ) + Real.eulerMascheroniConstant +
        Real.log (Real.log (Real.log ((M:ℕ):ℝ))))
      = Real.exp Real.eulerMascheroniConstant * (M:ℝ) * Real.log (Real.log ((M:ℕ):ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hMpos, Real.exp_log hllpos]
    ring
  rwa [hrhs] at hexp

lemma eps_le_Fq {ξ : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (hε : 0 < ε)
    (ha : 1 ≤ ⌊muF ξ ε⌋₊) : ε ≤ Fq ξ 1 := by
  have hμ0 : 0 ≤ muF ξ ε := muF_nonneg hξp.two_le hε
  have h1 : (1:ℝ) ≤ muF ξ ε := by simpa using (Nat.le_floor_iff hμ0).mp ha
  have := (Commons.NumberTheory.Robin.caMu_ge_iff_caF ξ ε 1 hξp.two_le hε le_rfl).mp (by simpa [muF] using h1)
  simpa [Fq] using this

lemma eps_gt_Fq1531 {ξ : ℕ} {ε : ℝ} (hε : 0 < ε) (h1531 : ¬ (1 ≤ ⌊muF 1531 ε⌋₊)) :
    Fq 1531 1 < ε := by
  by_contra hcon
  push_neg at hcon
  have hμ0 : 0 ≤ muF 1531 ε := muF_nonneg (by norm_num) hε
  have h1 : (1:ℝ) ≤ muF 1531 ε :=
    (by simpa [muF] using (Commons.NumberTheory.Robin.caMu_ge_iff_caF 1531 ε 1 (by norm_num) hε le_rfl).mpr (by simpa [Fq] using hcon))
  exact h1531 ((Nat.le_floor_iff hμ0).mpr (by simpa using h1))


-- ================= numeric preparations for the small cases =================
lemma log1529_lt : Real.log 1529 < 7.7 := by
  have h1 : Real.log 1529 < Real.log ((2:ℝ) ^ 11) := Real.log_lt_log (by norm_num) (by norm_num)
  have h1' : Real.log ((2:ℝ) ^ 11) = 11 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [h1'] at h1
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3 : (11:ℝ) * Real.log 2 < 11 * 0.6931471808 := by linarith
  linarith

lemma Fq17_lt_two_div : Fq 17 1 < 2 / Real.log 1529 := by
  have h17 : (0:ℝ) < Real.log 17 := Real.log_pos (by norm_num)
  have h2l : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1529 : (0:ℝ) < Real.log 1529 := Real.log_pos (by norm_num)
  have h4 : 4 * Real.log 2 ≤ Real.log 17 := by
    have h : Real.log ((2:ℝ)^4) ≤ Real.log 17 := Real.log_le_log (by norm_num) (by norm_num)
    have h' : Real.log ((2:ℝ)^4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [h']
  have hlog18 : Real.log (1 + 1/(17:ℝ)) ≤ 1/17 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/17 by norm_num)
    linarith [h]
  have h4pos : (0:ℝ) < 4 * Real.log 2 := by linarith
  have hmain : Real.log (1 + 1/(17:ℝ)) / Real.log 17 ≤ (1/17)/(4 * Real.log 2) := by
    rw [div_le_div_iff₀ h17 h4pos]
    nlinarith [hlog18, h4, h4pos, h17]
  rw [Fq_eq 17 (by norm_num)]
  refine hmain.trans_lt ?_
  have hlt : Real.log 1529 < 7.7 := log1529_lt
  have h2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2g : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  rw [div_lt_div_iff₀ h4pos hlog1529]
  nlinarith [hlt, h2u, h2g, h2l]

lemma Fq13_lt_two_div : Fq 13 1 < 2 / Real.log (1529:ℝ) := by
  have hlog13 : (2:ℝ) < Real.log (13:ℝ) := by
    have h1 : Real.exp 2 < (13:ℝ) := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have h3 := Real.exp_one_lt_three
      rw [h2]; nlinarith [Real.exp_pos 1]
    calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ < Real.log (13:ℝ) := Real.log_lt_log (Real.exp_pos 2) h1
  have hlog1529 : (0:ℝ) < Real.log (1529:ℝ) := Real.log_pos (by norm_num)
  have hlt : Real.log (1529:ℝ) < 7.7 := log1529_lt
  have hle := Commons.NumberTheory.Robin.caF1_le_inv_mul_log (p := 13) (by norm_num)
  have hA : Fq 13 1 ≤ 1/(13 * Real.log (13:ℝ)) := by simpa [Fq] using hle
  have h13pos : (0:ℝ) < 13 * Real.log (13:ℝ) := by nlinarith
  have hStep : Fq 13 1 * Real.log (1529:ℝ) < 2 := by
    have h2 : (1:ℝ)/(13 * Real.log (13:ℝ)) * Real.log (1529:ℝ) < 2 := by
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff₀ h13pos]
      nlinarith [hlog13, hlt]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hA (le_of_lt hlog1529)) h2
  exact (lt_div_iff₀ hlog1529).mpr hStep

-- general "level zero implies epsilon beyond the threshold" fact
lemma eps_gt_Fq_of_floor_zero {q : ℕ} {ε : ℝ} (hq : 2 ≤ q) (hε : 0 < ε)
    (h0 : ⌊muF q ε⌋₊ = 0) : Fq q 1 < ε := by
  by_contra hcon
  push_neg at hcon
  have h1 : (1:ℝ) ≤ muF q ε := by
    have hh := (Commons.NumberTheory.Robin.caMu_ge_iff_caF q ε 1 hq hε le_rfl).mpr
      (by simpa [Fq] using hcon)
    simpa [muF] using hh
  have h2 : 1 ≤ ⌊muF q ε⌋₊ := (Nat.le_floor_iff (muF_nonneg hq hε)).mpr (by simpa using h1)
  omega

-- case B : epsilon is large
lemma Fq_lt_eps_of_large {q m : ℕ} {ε : ℝ} (hq2 : 2 ≤ q) (hm : 1 < m) (hε : 0 < ε)
    (hbig : Real.exp (2/ε) ≤ (q:ℝ) - 2) (hle : (q:ℝ) - 2 ≤ (m:ℝ))
    (hFq : Fq q 1 < 2 / Real.log m) : Fq q 1 < ε := by
  have hlogm : (0:ℝ) < Real.log m := Real.log_pos (by exact_mod_cast hm)
  have hq2r : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
  have h1 : (1:ℝ) < Real.exp (2/ε) := Real.one_lt_exp_iff.mpr (by positivity)
  have h1b : 2/ε ≤ Real.log ((q:ℝ) - 2) := by
    rw [← Real.log_exp (2/ε)]
    exact Real.log_le_log (Real.exp_pos _) hbig
  have h2 : Real.log ((q:ℝ) - 2) ≤ Real.log m := Real.log_le_log (by linarith) hle
  have h3 : 2/ε ≤ Real.log m := h1b.trans h2
  have h4 : 2 / Real.log m ≤ ε := by
    rw [div_le_iff₀ hlogm]
    have h5 := (div_le_iff₀ hε).mp h3
    linarith
  linarith

-- ================= the xi = 13 case =================
def lv13 : ℕ → ℕ → ℕ := fun b p =>
  if p = 2 then (if b % 2 = 0 then 5 else 4)
  else if p = 3 then (if b = 0 ∨ b = 1 ∨ b = 4 ∨ b = 5 then 3 else 2)
  else if p = 5 then (if b ≤ 3 then 2 else 1)
  else 1

def LIT13 : ℕ → ℚ := fun b =>
  if b = 0 then 1413337/500000 else if b = 1 then 2784767/1000000 else if b = 2 then 1379707/500000
  else if b = 3 then 108581/40000 else if b = 4 then 2726529/1000000 else if b = 5 then 335013/125000
  else if b = 6 then 2651913/1000000 else 13009/5000

def E13 (b : ℕ) : ℚ := ∑ p ∈ pfS 13, (lv13 b p : ℚ) * lbF p

def U13 (b : ℕ) : ℚ := ∑ p ∈ pfS 13, ubF p (lv13 b p)

theorem chk13_check : (List.range 8).all (fun b => decide (
    LIT13 b ≤ logLower (E13 b) ∧ U13 b ≤ (57711:ℚ)/100000 + logLower (LIT13 b) ∧
    (1:ℚ) < LIT13 b ∧ LIT13 b < (2:ℚ)^logDepth ∧ (1:ℚ) < E13 b ∧ E13 b < (2:ℚ)^logDepth ∧
    (1:ℚ) < logLower (E13 b))) = true := by decide +kernel

def chk13 (b : ℕ) : Prop :=
    LIT13 b ≤ logLower (E13 b) ∧ U13 b ≤ (57711:ℚ)/100000 + logLower (LIT13 b) ∧
    (1:ℚ) < LIT13 b ∧ LIT13 b < (2:ℚ)^logDepth ∧ (1:ℚ) < E13 b ∧ E13 b < (2:ℚ)^logDepth ∧
    (1:ℚ) < logLower (E13 b)

lemma chk13_of {b : ℕ} (hb : b < 8) : chk13 b := by
  have h1 := List.all_eq_true.mp chk13_check b (by rw [List.mem_range]; exact hb)
  rw [decide_eq_true_eq] at h1
  exact h1

lemma hset13 : pfS 13 = ({2,3,5,7,11,13} : Finset ℕ) := by decide

lemma lv13_Kcap {b p : ℕ} (hb : b < 8) (hp : p ∈ ({2,3,5,7,11,13} : Finset ℕ)) :
    lv13 b p ≤ Kcap p := by
  fin_cases hp <;> (interval_cases b <;> decide)

lemma level_ge_of_le {p k : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (hle : ε ≤ Fq p k) : k ≤ ⌊muF p ε⌋₊ := by
  have h : (k:ℝ) ≤ muF p ε :=
    (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk).mpr hle
  exact (Nat.le_floor_iff (muF_nonneg hp hε)).mpr h

lemma level_lt_of_gt {p k : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (hgt : Fq p k < ε) : ⌊muF p ε⌋₊ < k := by
  have hnot : ¬ ((k:ℝ) ≤ muF p ε) := by
    intro hc
    have h := (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk).mp hc
    exact absurd h (not_le.mpr hgt)
  have h2 : muF p ε < (k:ℝ) := not_le.mp hnot
  have h3 : (((⌊muF p ε⌋₊ : ℕ)) : ℝ) ≤ muF p ε := Nat.floor_le (muF_nonneg hp hε)
  by_contra hc
  push_neg at hc
  have h4 : (k:ℝ) ≤ (((⌊muF p ε⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hc
  linarith

lemma level_eq_of_le {p k : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (hle : ε ≤ Fq p k) (hupper : ⌊muF p ε⌋₊ ≤ k) : ⌊muF p ε⌋₊ = k :=
  le_antisymm hupper (level_ge_of_le hp hε hk hle)

lemma level_eq_of_gt {p k : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (hgt : Fq p k < ε) (hlower : k - 1 ≤ ⌊muF p ε⌋₊) : ⌊muF p ε⌋₊ = k - 1 := by
  have h := level_lt_of_gt hp hε hk hgt
  omega

lemma a_le_kmaxC17 {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hlt : p < 17) (hε : 0 < ε)
    (hge : Fq 17 1 ≤ ε) : ⌊muF p ε⌋₊ ≤ kmaxC 17 p :=
  a_le_kmaxC (by decide) hp hlt (by norm_num) hε hge

lemma a_ge_kminC13 {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hle13 : p ≤ 13) (hε : 0 < ε)
    (hm : ε ≤ Fq 13 1) : kminC 13 p ≤ ⌊muF p ε⌋₊ :=
  a_ge_kminC (by norm_num) hp hle13 hε hm

lemma levels_big3 {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ Fq 13 1) (hεgt : Fq 17 1 < ε) :
    ⌊muF 7 ε⌋₊ = 1 ∧ ⌊muF 11 ε⌋₊ = 1 ∧ ⌊muF 13 ε⌋₊ = 1 := by
  have h17ge : Fq 17 1 ≤ ε := le_of_lt hεgt
  have hbr : ∀ p : ℕ, p ∈ ({7,11,13} : Finset ℕ) →
      kminC 13 p = 1 ∧ kmaxC 17 p = 1 ∧ Nat.Prime p := by
    intro p hp
    fin_cases hp <;> refine ⟨?_, ?_, by decide⟩ <;> decide
  constructor
  · have h := hbr 7 (by decide)
    have h1 : kminC 13 7 ≤ ⌊muF 7 ε⌋₊ := a_ge_kminC13 h.2.2 (by norm_num) hε hεle
    have h2 : ⌊muF 7 ε⌋₊ ≤ kmaxC 17 7 := a_le_kmaxC17 h.2.2 (by norm_num) hε h17ge
    omega
  constructor
  · have h := hbr 11 (by decide)
    have h1 : kminC 13 11 ≤ ⌊muF 11 ε⌋₊ := a_ge_kminC13 h.2.2 (by norm_num) hε hεle
    have h2 : ⌊muF 11 ε⌋₊ ≤ kmaxC 17 11 := a_le_kmaxC17 h.2.2 (by norm_num) hε h17ge
    omega
  · have h := hbr 13 (by decide)
    have h1 : kminC 13 13 ≤ ⌊muF 13 ε⌋₊ := a_ge_kminC13 h.2.2 (by norm_num) hε hεle
    have h2 : ⌊muF 13 ε⌋₊ ≤ kmaxC 17 13 := a_le_kmaxC17 h.2.2 (by norm_num) hε h17ge
    omega

lemma exp_step {M : ℕ} (hσp : (0:ℝ) < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ))
    (hMpos : (0:ℝ) < (M:ℝ)) (hlogM1 : (1:ℝ) < Real.log ((M:ℕ):ℝ))
    (hlog : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) ≤
      Real.log ((M:ℕ):ℝ) + Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ)))) :
    ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log ((M:ℕ):ℝ)) := by
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hσp] at hexp
  have hllpos : 0 < Real.log (Real.log ((M:ℕ):ℝ)) := Real.log_pos hlogM1
  have hrhs : Real.exp (Real.log ((M:ℕ):ℝ) + Real.eulerMascheroniConstant +
        Real.log (Real.log (Real.log ((M:ℕ):ℝ))))
      = Real.exp Real.eulerMascheroniConstant * (M:ℝ) * Real.log (Real.log ((M:ℕ):ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hMpos, Real.exp_log hllpos]
    ring
  rwa [hrhs] at hexp

-- ================= the xi = 13 case =================
lemma robin13_aux {M : ℕ} {ε : ℝ} {b : ℕ}
    (hε : 0 < ε) (hM : M = ∏ p ∈ pfS 13, p ^ ⌊muF p ε⌋₊)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ 13 → 1 ≤ ⌊muF q ε⌋₊)
    (hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 b p) (hb : b < 8) (hchk : chk13 b) :
    Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
  obtain ⟨hLIT, hCHK, hLIT1, hLITlt, hE1, hElt, hElit1⟩ := hchk
  have hlogM : Real.log ((M:ℕ):ℝ) = ∑ p ∈ pfS 13, ((⌊muF p ε⌋₊ : ℕ) : ℝ) * Real.log (p:ℝ) := by
    rw [hM, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact ne_of_gt (by exact_mod_cast (pow_pos (Finset.mem_filter.mp hp).2.pos _))
  have hub : ∑ p ∈ pfS 13, Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ)) ≤ ((U13 b : ℚ) : ℝ) := by
    have hU : ((U13 b : ℚ) : ℝ) = ∑ p ∈ pfS 13, ((ubF p (lv13 b p) : ℚ) : ℝ) := by
      simp only [U13]
      push_cast
      ring_nf
    rw [hU]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hple : p ≤ 13 := by
      have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
    have hp6 : p ∈ ({2,3,5,7,11,13} : Finset ℕ) := by rw [← hset13]; exact hp
    have hlv : ⌊muF p ε⌋₊ = lv13 b p := hlev p hp
    have hK1 : 1 ≤ lv13 b p := by
      have h := hsupp p hpp hple
      omega
    have hKcap : lv13 b p ≤ Kcap p := lv13_Kcap hb hp6
    have hge1 : (1:ℚ) ≤ rq p (lv13 b p) := rq_ge_one' hpp.two_le hK1
    have hlt2 : rq p (lv13 b p) < 2 ^ logDepth := rq_lt_depth' hpp.two_le
    have hleaf := ubLeafAll p (lv13 b p) hK1 hKcap (mem_plistB_of hpp (by omega : p < 1530))
    have h1 : Real.log (((rq p (⌊muF p ε⌋₊) : ℚ) : ℝ)) ≤ Real.log (((rq p (lv13 b p) : ℚ) : ℝ)) := by
      rw [hlv]
    have h2 : Real.log (((rq p (lv13 b p) : ℚ) : ℝ)) ≤ ((ubF p (lv13 b p) : ℚ) : ℝ) :=
      (logUpper_ge_log (rq p (lv13 b p)) (by exact_mod_cast hge1) hlt2).trans (by exact_mod_cast hleaf)
    exact h1.trans h2
  have hElog : ((E13 b : ℚ) : ℝ) ≤ Real.log ((M:ℕ):ℝ) := by
    have hE : ((E13 b : ℚ) : ℝ) = ∑ p ∈ pfS 13, ((lv13 b p : ℚ) : ℝ) * ((lbF p : ℚ) : ℝ) := by
      simp only [E13]
      push_cast
      ring_nf
    rw [hlogM, hE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hple : p ≤ 13 := by
      have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
    have hp1530 : p < 1530 := by omega
    have hp6 : p ∈ ({2,3,5,7,11,13} : Finset ℕ) := by rw [← hset13]; exact hp
    have hle : ((lv13 b p : ℚ) : ℝ) ≤ ((⌊muF p ε⌋₊ : ℕ) : ℝ) := by
      rw [hlev p hp]; push_cast; exact le_rfl
    have hlb : ((lbF p : ℚ) : ℝ) ≤ Real.log (p:ℝ) := by
      have h1 : lbF p ≤ logLower (p:ℚ) := lbLeafAll p (mem_plistB_of hpp hp1530)
      have h1' : ((lbF p : ℚ) : ℝ) ≤ ((logLower (p:ℚ) : ℚ) : ℝ) := by exact_mod_cast h1
      have h2 : ((logLower (p:ℚ) : ℚ) : ℝ) ≤ Real.log (p:ℝ) := by
        have hh := logLower_le_log (p:ℚ) (by exact_mod_cast hpp.one_le)
          (by exact_mod_cast (by omega : p < 8192))
        simpa using hh
      exact h1'.trans h2
    have hb0 : (0:ℝ) ≤ ((lbF p : ℚ) : ℝ) := by
      have hbr : lbF p = (lbNon p : ℚ)/1000000000000 := getC lbF_bridge_all hpp hp1530
      rw [hbr]; positivity
    exact mul_le_mul hle hlb hb0 (by positivity)
  have hstep1 : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ) ≤
      (57711:ℝ)/100000 + ((logLower (LIT13 b) : ℚ) : ℝ) := by
    have h1 : ((U13 b : ℚ) : ℝ) ≤ (57711:ℝ)/100000 + ((logLower (LIT13 b) : ℚ) : ℝ) := by
      have hh : ((U13 b : ℚ) : ℝ) ≤ (((57711:ℚ)/100000 + logLower (LIT13 b) : ℚ) : ℝ) := by
        exact_mod_cast hCHK
      simpa using hh
    rw [log_ratio_eq hM]
    exact hub.trans h1
  have hLIT1r : (1:ℝ) < (LIT13 b : ℝ) := by exact_mod_cast hLIT1
  have hE1r : (1:ℝ) < (E13 b : ℝ) := by exact_mod_cast hE1
  have h2 : ((logLower (LIT13 b) : ℚ) : ℝ) ≤ Real.log (LIT13 b : ℝ) :=
    logLower_le_log (LIT13 b) (le_of_lt hLIT1) hLITlt
  have h3 : Real.log (LIT13 b : ℝ) ≤ Real.log (Real.log (E13 b : ℝ)) := by
    refine Real.log_le_log (by linarith [hLIT1r] : (0:ℝ) < (LIT13 b : ℝ)) ?_
    exact (by exact_mod_cast hLIT : (LIT13 b : ℝ) ≤ ((logLower (E13 b) : ℚ) : ℝ)).trans
      (logLower_le_log (E13 b) (le_of_lt hE1) hElt)
  have h4 : Real.log (Real.log (E13 b : ℝ)) ≤ Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    refine Real.log_le_log (Real.log_pos hE1r) ?_
    exact Real.log_le_log (by linarith [hE1r] : (0:ℝ) < (E13 b : ℝ)) hElog
  have h5' : (57711:ℝ)/100000 ≤ Real.eulerMascheroniConstant := by
    have hh := gammaLo_le
    rw [Rat.cast_div] at hh
    norm_num at hh
    exact hh
  calc Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ)
      ≤ (57711:ℝ)/100000 + ((logLower (LIT13 b) : ℚ) : ℝ) := hstep1
    _ ≤ (57711:ℝ)/100000 + Real.log (LIT13 b : ℝ) := by linarith [h2]
    _ ≤ (57711:ℝ)/100000 + Real.log (Real.log (E13 b : ℝ)) := by linarith [h3]
    _ ≤ (57711:ℝ)/100000 + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by linarith [h4]
    _ ≤ Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by linarith [h5']

lemma robin13_chain {M : ℕ} {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ Fq 13 1) (hεgt17 : Fq 17 1 < ε)
    (hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ 13 → 1 ≤ ⌊muF q ε⌋₊)
    (hM : M = ∏ p ∈ pfS 13, p ^ ⌊muF p ε⌋₊) :
    ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ)) := by
  obtain ⟨hv7, hv11, hv13⟩ := levels_big3 hε hεle hεgt17
  have h17ge : Fq 17 1 ≤ ε := le_of_lt hεgt17
  have hMpos : (0:ℝ) < (M:ℝ) := by
    have h : 0 < M := by rw [hM]; exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    exact_mod_cast h
  have hσpos : (0:ℝ) < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) := by
    have h : 0 < M := by rw [hM]; exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    exact_mod_cast (ArithmeticFunction.sigma_pos_iff (k := 1)).2 h
  have hlogM1 : (1:ℝ) < Real.log ((M:ℕ):ℝ) := by
    have hkey : (30030:ℝ) ≤ (M:ℝ) := by
      have hMge : 30030 ≤ M := by
        rw [hM]
        have h1 : 30030 = ∏ p ∈ pfS 13, p ^ (1:ℕ) := by decide
        rw [h1]
        refine Finset.prod_le_prod' ?_
        · intro p hp
          have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hple : p ≤ 13 := by have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
          exact pow_le_pow_right₀ (le_of_lt hpp.one_lt) (hsupp p hpp hple)
      exact_mod_cast hMge
    have h1 : Real.log 30030 ≤ Real.log ((M:ℕ):ℝ) := Real.log_le_log (by norm_num) hkey
    have h2 : Real.exp 1 < 30030 := by have := Real.exp_one_lt_d9; linarith
    have h3 : (1:ℝ) < Real.log 30030 := by
      rw [← Real.log_exp (1:ℝ)]
      exact Real.log_lt_log (Real.exp_pos 1) h2
    linarith
  have hkey : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) - Real.log ((M:ℕ):ℝ) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    by_cases h52 : ε ≤ Fq 5 2
    · by_cases h33 : ε ≤ Fq 3 3
      · by_cases h25 : ε ≤ Fq 2 5
        · -- b = 0
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 0 5 := by
            have hk : lv13 0 5 = 2 := by decide
            rw [hk]
            refine level_eq_of_le (p := 5) (k := 2) (by norm_num) hε (by norm_num) h52 ?_
            have hb := a_le_kmaxC17 (p := 5) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 5 = 2 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 0 3 := by
            have hk : lv13 0 3 = 3 := by decide
            rw [hk]
            refine level_eq_of_le (p := 3) (k := 3) (by norm_num) hε (by norm_num) h33 ?_
            have hb := a_le_kmaxC17 (p := 3) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 3 = 3 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 0 2 := by
            have hk : lv13 0 2 = 5 := by decide
            rw [hk]
            refine level_eq_of_le (p := 2) (k := 5) (by norm_num) hε (by norm_num) h25 ?_
            have hb := a_le_kmaxC17 (p := 2) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 2 = 5 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 0 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
        · -- b = 1
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 1 5 := by
            have hk : lv13 1 5 = 2 := by decide
            rw [hk]
            refine level_eq_of_le (p := 5) (k := 2) (by norm_num) hε (by norm_num) h52 ?_
            have hb := a_le_kmaxC17 (p := 5) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 5 = 2 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 1 3 := by
            have hk : lv13 1 3 = 3 := by decide
            rw [hk]
            refine level_eq_of_le (p := 3) (k := 3) (by norm_num) hε (by norm_num) h33 ?_
            have hb := a_le_kmaxC17 (p := 3) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 3 = 3 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 1 2 := by
            have hk : lv13 1 2 = 4 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 2) (k := 5) (by norm_num) hε (by norm_num) (not_le.mp h25) ?_
            have hb := a_ge_kminC13 (p := 2) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 2 = 4 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 1 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
      · by_cases h25 : ε ≤ Fq 2 5
        · -- b = 2
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 2 5 := by
            have hk : lv13 2 5 = 2 := by decide
            rw [hk]
            refine level_eq_of_le (p := 5) (k := 2) (by norm_num) hε (by norm_num) h52 ?_
            have hb := a_le_kmaxC17 (p := 5) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 5 = 2 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 2 3 := by
            have hk : lv13 2 3 = 2 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 3) (k := 3) (by norm_num) hε (by norm_num) (not_le.mp h33) ?_
            have hb := a_ge_kminC13 (p := 3) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 3 = 2 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 2 2 := by
            have hk : lv13 2 2 = 5 := by decide
            rw [hk]
            refine level_eq_of_le (p := 2) (k := 5) (by norm_num) hε (by norm_num) h25 ?_
            have hb := a_le_kmaxC17 (p := 2) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 2 = 5 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 2 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
        · -- b = 3
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 3 5 := by
            have hk : lv13 3 5 = 2 := by decide
            rw [hk]
            refine level_eq_of_le (p := 5) (k := 2) (by norm_num) hε (by norm_num) h52 ?_
            have hb := a_le_kmaxC17 (p := 5) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 5 = 2 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 3 3 := by
            have hk : lv13 3 3 = 2 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 3) (k := 3) (by norm_num) hε (by norm_num) (not_le.mp h33) ?_
            have hb := a_ge_kminC13 (p := 3) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 3 = 2 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 3 2 := by
            have hk : lv13 3 2 = 4 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 2) (k := 5) (by norm_num) hε (by norm_num) (not_le.mp h25) ?_
            have hb := a_ge_kminC13 (p := 2) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 2 = 4 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 3 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
    · by_cases h33 : ε ≤ Fq 3 3
      · by_cases h25 : ε ≤ Fq 2 5
        · -- b = 4
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 4 5 := by
            have hk : lv13 4 5 = 1 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 5) (k := 2) (by norm_num) hε (by norm_num) (not_le.mp h52) ?_
            have hb := a_ge_kminC13 (p := 5) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 5 = 1 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 4 3 := by
            have hk : lv13 4 3 = 3 := by decide
            rw [hk]
            refine level_eq_of_le (p := 3) (k := 3) (by norm_num) hε (by norm_num) h33 ?_
            have hb := a_le_kmaxC17 (p := 3) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 3 = 3 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 4 2 := by
            have hk : lv13 4 2 = 5 := by decide
            rw [hk]
            refine level_eq_of_le (p := 2) (k := 5) (by norm_num) hε (by norm_num) h25 ?_
            have hb := a_le_kmaxC17 (p := 2) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 2 = 5 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 4 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
        · -- b = 5
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 5 5 := by
            have hk : lv13 5 5 = 1 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 5) (k := 2) (by norm_num) hε (by norm_num) (not_le.mp h52) ?_
            have hb := a_ge_kminC13 (p := 5) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 5 = 1 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 5 3 := by
            have hk : lv13 5 3 = 3 := by decide
            rw [hk]
            refine level_eq_of_le (p := 3) (k := 3) (by norm_num) hε (by norm_num) h33 ?_
            have hb := a_le_kmaxC17 (p := 3) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 3 = 3 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 5 2 := by
            have hk : lv13 5 2 = 4 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 2) (k := 5) (by norm_num) hε (by norm_num) (not_le.mp h25) ?_
            have hb := a_ge_kminC13 (p := 2) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 2 = 4 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 5 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
      · by_cases h25 : ε ≤ Fq 2 5
        · -- b = 6
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 6 5 := by
            have hk : lv13 6 5 = 1 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 5) (k := 2) (by norm_num) hε (by norm_num) (not_le.mp h52) ?_
            have hb := a_ge_kminC13 (p := 5) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 5 = 1 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 6 3 := by
            have hk : lv13 6 3 = 2 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 3) (k := 3) (by norm_num) hε (by norm_num) (not_le.mp h33) ?_
            have hb := a_ge_kminC13 (p := 3) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 3 = 2 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 6 2 := by
            have hk : lv13 6 2 = 5 := by decide
            rw [hk]
            refine level_eq_of_le (p := 2) (k := 5) (by norm_num) hε (by norm_num) h25 ?_
            have hb := a_le_kmaxC17 (p := 2) (by decide) (by norm_num) hε h17ge
            have hk2 : kmaxC 17 2 = 5 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 6 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
        · -- b = 7
          have hv5 : ⌊muF 5 ε⌋₊ = lv13 7 5 := by
            have hk : lv13 7 5 = 1 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 5) (k := 2) (by norm_num) hε (by norm_num) (not_le.mp h52) ?_
            have hb := a_ge_kminC13 (p := 5) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 5 = 1 := by decide
            omega
          have hv3 : ⌊muF 3 ε⌋₊ = lv13 7 3 := by
            have hk : lv13 7 3 = 2 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 3) (k := 3) (by norm_num) hε (by norm_num) (not_le.mp h33) ?_
            have hb := a_ge_kminC13 (p := 3) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 3 = 2 := by decide
            omega
          have hv2 : ⌊muF 2 ε⌋₊ = lv13 7 2 := by
            have hk : lv13 7 2 = 4 := by decide
            rw [hk]
            refine level_eq_of_gt (p := 2) (k := 5) (by norm_num) hε (by norm_num) (not_le.mp h25) ?_
            have hb := a_ge_kminC13 (p := 2) (by decide) (by norm_num) hε hεle
            have hk2 : kminC 13 2 = 4 := by decide
            omega
          have hlev : ∀ p ∈ pfS 13, ⌊muF p ε⌋₊ = lv13 7 p := by
            intro p hp
            have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hple : p ≤ 13 := by
              have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
            have h2p : 2 ≤ p := hpp.two_le
            interval_cases p <;> first
              | (exfalso; revert hpp; decide)
              | assumption
              | (simp only [lv13]; first | exact hv7 | exact hv11 | exact hv13)
          exact robin13_aux hε hM hsupp hlev (by norm_num) (chk13_of (by norm_num))
  have hlogσ : Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)) ≤
      Real.log ((M:ℕ):ℝ) + Real.eulerMascheroniConstant + Real.log (Real.log (Real.log ((M:ℕ):ℝ))) := by
    linarith
  exact exp_step hσpos hMpos hlogM1 hlogσ

-- ================= the xi <= 11 case =================
lemma robin11_contra {M ξ : ℕ} {ε : ℝ} (hξp : Nat.Prime ξ) (hξle11 : ξ ≤ 11)
    (hε : 0 < ε) (hεgt13 : Fq 13 1 < ε) (hM : M = ∏ p ∈ pfS ξ, p ^ ⌊muF p ε⌋₊) :
    M ≤ 55440 := by
  have hle : M ≤ ∏ p ∈ pfS 11, p ^ kmaxC 13 p := by
    rw [hM]
    refine (Finset.prod_le_prod' (g := fun p : ℕ => p ^ kmaxC 13 p) ?_).trans ?_
    · intro p hp
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hpξ : p ≤ ξ := by have h := (Finset.mem_filter.mp hp).1; simp only [Finset.mem_range] at h; omega
      have hlt : p < 13 := by have : p ≤ 11 := le_trans hpξ hξle11; omega
      exact pow_le_pow_right₀ (le_of_lt hpp.one_lt)
        (a_le_kmaxC (by decide) hpp hlt (by norm_num) hε (le_of_lt hεgt13))
    · apply Finset.prod_le_prod_of_subset_of_one_le' (pfS_subset_pfS hξle11)
      intro p hp hp'
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      exact one_le_pow₀ (le_of_lt hpp.one_lt)
  have h2 : (∏ p ∈ pfS 11, p ^ kmaxC 13 p) = 55440 := by decide
  exact hle.trans (le_of_eq h2)

-- ================= the generic "outside the support" argument =================
lemma eps_gt_of_notin_range {q m : ℕ} {ε : ℝ} {S T : Finset ℕ}
    (hSeq : S = (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
    (hTeq : T = S.filter (fun p : ℕ => 1 ≤ ⌊muF p ε⌋₊))
    (hq : Nat.Prime q) (hqnT : q ∉ T) (hε : 0 < ε)
    (hm : 1 < m) (hqm : q ≤ m + 2) (hFq : Fq q 1 < 2 / Real.log m) : Fq q 1 < ε := by
  by_cases hqS : q ∈ S
  · have h0 : ⌊muF q ε⌋₊ = 0 := by
      have h : ¬ (1 ≤ ⌊muF q ε⌋₊) := fun hc => hqnT (by rw [hTeq]; exact Finset.mem_filter.mpr ⟨hqS, hc⟩)
      omega
    exact eps_gt_Fq_of_floor_zero hq.two_le hε h0
  · have hbig : Nat.ceil (Real.exp (2 / ε)) + 2 ≤ q := by
      by_contra hcon
      push_neg at hcon
      exact hqS (by rw [hSeq]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩)
    have h1 : Real.exp (2/ε) ≤ (q:ℝ) - 2 := by
      have h3 : Nat.ceil (Real.exp (2/ε)) ≤ q - 2 := by omega
      have h4 : ((q - 2 : ℕ) : ℝ) = (q:ℝ) - 2 := Nat.cast_sub hq.two_le
      have h5 : (Nat.ceil (Real.exp (2/ε)) : ℝ) ≤ (q:ℝ) - 2 := by rw [← h4]; exact_mod_cast h3
      have h6 : Real.exp (2/ε) ≤ (Nat.ceil (Real.exp (2/ε)) : ℝ) := Nat.le_ceil _
      linarith
    have h2 : (q:ℝ) - 2 ≤ (m:ℝ) := by
      have h4 : ((q - 2 : ℕ) : ℝ) = (q:ℝ) - 2 := Nat.cast_sub hq.two_le
      rw [← h4]
      exact_mod_cast (by omega : q - 2 ≤ m)
    exact Fq_lt_eps_of_large hq.two_le hm hε h1 h2 hFq

theorem primes_le_1523 : (((List.range 1530).filter (fun p => isPrimeC p)).all
    (fun p => decide (p ≤ 1523))) = true := by decide +kernel

-- ================= the main statement =================
theorem robin_caFval_aux : ∀ M : ℕ,
    (∃ ε : ℝ, 0 < ε ∧
      (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
        (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
          ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = M ∧
      (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
        (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
          ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).sup id < 1530) →
    55441 ≤ M →
    ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ)) := by
  intro M hdata h55441
  obtain ⟨ε, hεpos, hprod, hsup⟩ := hdata
  let S : Finset ℕ := (Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime
  let T : Finset ℕ := S.filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
      ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)
  have hprodS : Finset.prod S (fun p : ℕ => p ^ ⌊muF p ε⌋₊) = M := hprod
  have hsupT : T.sup id < 1530 := hsup
  have hTne : T.Nonempty :=
    caSupp_nonempty_of_two_le hεpos (by rw [hprod]; omega)
  set ξ : ℕ := T.max' hTne with hξdef
  have hTeq : T = pfS ξ := by
    rw [hξdef]
    exact caSupp_eq_primesLE_xi hεpos hTne
  have hξT : ξ ∈ T := by rw [hξdef]; exact Finset.max'_mem T hTne
  have hξS : ξ ∈ S := (Finset.mem_filter.mp hξT).1
  have hξprime : Nat.Prime ξ := (Finset.mem_filter.mp hξS).2
  have hξact : 1 ≤ ⌊muF ξ ε⌋₊ := (Finset.mem_filter.mp hξT).2
  have hξ1530 : ξ < 1530 := by
    have h : ξ ≤ T.sup id := Finset.le_sup (f := id) hξT
    omega
  have hξ1523 : ξ ≤ 1523 := getC primes_le_1523 hξprime hξ1530
  have hsupp : ∀ q : ℕ, Nat.Prime q → q ≤ ξ → 1 ≤ ⌊muF q ε⌋₊ := by
    intro q hq hqle
    have hqT : q ∈ T := by
      rw [hTeq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
    exact (Finset.mem_filter.mp hqT).2
  have hM : M = ∏ p ∈ pfS ξ, p ^ ⌊muF p ε⌋₊ := by
    have hMT : ∏ p ∈ T, p ^ ⌊muF p ε⌋₊ = M := by
      change ∏ p ∈ S.filter (fun p : ℕ => 1 ≤ ⌊muF p ε⌋₊), p ^ ⌊muF p ε⌋₊ = M
      rw [Finset.prod_filter]
      rw [← hprodS]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : 1 ≤ ⌊muF p ε⌋₊
      · rw [if_pos h]
      · rw [if_neg h]
        have hz : ⌊muF p ε⌋₊ = 0 := by omega
        simp [hz]
    rw [← hMT, hTeq]
  by_cases h17 : 17 ≤ ξ
  · have hεle : ε ≤ Fq ξ 1 := eps_le_Fq hξprime hεpos hξact
    have hεgt : Fq (nxF ξ) 1 < ε := by
      obtain ⟨ha_le, hb_ge, hnx_le, hnx1531, hξ1523', hblk80⟩ := blk_facts hξprime h17 hξ1523
      have hnxFp : Nat.Prime (nxF ξ) := nxF_prime hξprime h17 hξ1523
      have hnxFgt : ξ < nxF ξ := nxF_gt hξprime h17 hξ1523
      have hnotT : nxF ξ ∉ T := by
        rw [hTeq]
        intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hFqle : Fq (nxF ξ) 1 ≤ Fq 17 1 :=
        Fq_mono (by norm_num : 2 ≤ 17) hnxFp.two_le (le_trans h17 (le_of_lt hnxFgt))
      exact eps_gt_of_notin_range (S := S) (T := T) rfl rfl hnxFp hnotT hεpos
        (m := 1529) (by norm_num) (by omega) (by linarith [hFqle, Fq17_lt_two_div])
    exact robin_bound_block hξprime h17 hξ1523 hεpos hεgt hsupp hεle hM
  · have hξle16 : ξ ≤ 16 := by omega
    have hmem6 : ξ ∈ ({2,3,5,7,11,13} : Finset ℕ) := by
      have hset : (Finset.Icc 2 16).filter Nat.Prime = ({2,3,5,7,11,13} : Finset ℕ) := by decide
      rw [← hset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hξprime.two_le, hξle16⟩, hξprime⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem6
    rcases hmem6 with h2 | h3 | h5 | h7 | h11 | h13
    · exfalso
      have h13notT : (13:ℕ) ∉ T := by
        rw [hTeq]; intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt13 : Fq 13 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h13notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq13_lt_two_div
      have hle := robin11_contra hξprime (by omega) hεpos hεgt13 hM
      omega
    · exfalso
      have h13notT : (13:ℕ) ∉ T := by
        rw [hTeq]; intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt13 : Fq 13 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h13notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq13_lt_two_div
      have hle := robin11_contra hξprime (by omega) hεpos hεgt13 hM
      omega
    · exfalso
      have h13notT : (13:ℕ) ∉ T := by
        rw [hTeq]; intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt13 : Fq 13 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h13notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq13_lt_two_div
      have hle := robin11_contra hξprime (by omega) hεpos hεgt13 hM
      omega
    · exfalso
      have h13notT : (13:ℕ) ∉ T := by
        rw [hTeq]; intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt13 : Fq 13 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h13notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq13_lt_two_div
      have hle := robin11_contra hξprime (by omega) hεpos hεgt13 hM
      omega
    · exfalso
      have h13notT : (13:ℕ) ∉ T := by
        rw [hTeq]; intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt13 : Fq 13 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h13notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq13_lt_two_div
      have hle := robin11_contra hξprime (by omega) hεpos hεgt13 hM
      omega
    · rw [h13] at hξprime hξact hTeq hM
      have hεle13 : ε ≤ Fq 13 1 := eps_le_Fq hξprime hεpos hξact
      have hsupp13 : ∀ q : ℕ, Nat.Prime q → q ≤ 13 → 1 ≤ ⌊muF q ε⌋₊ := by
        intro q hq hqle
        have hqT : q ∈ T := by
          rw [hTeq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
        exact (Finset.mem_filter.mp hqT).2
      have h17notT : (17:ℕ) ∉ T := by
        rw [hTeq]
        intro hcon
        have h1 := (Finset.mem_filter.mp hcon).1
        simp only [Finset.mem_range] at h1
        omega
      have hεgt17 : Fq 17 1 < ε :=
        eps_gt_of_notin_range (S := S) (T := T) rfl rfl (by decide) h17notT hεpos
          (m := 1529) (by norm_num) (by norm_num) Fq17_lt_two_div
      exact robin13_chain hεpos hεle13 hεgt17 hsupp13 hM


end Commons.NumberTheory.Robin.RobinCaFval


namespace Commons.NumberTheory.Robin

theorem robin_caFval_small (h : RiemannHypothesis) :
    ∀ M : ℕ,
      (∃ ε : ℝ, 0 < ε ∧
        (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
          (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
            ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = M ∧
        (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
          (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
            ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).sup id < 1530) →
      55441 ≤ M →
      ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ)) :=
  fun M hdata h55441 => RobinCaFval.robin_caFval_aux M hdata h55441

end Commons.NumberTheory.Robin

