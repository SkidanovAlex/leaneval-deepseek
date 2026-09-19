import Mathlib.Algebra.Order.Star.Real

namespace Commons.NumberTheory.BombieriVinogradov

open Finset

lemma lam4_dyadic_sum_bound (x Q T L : ℝ) (J : ℕ) (hx : 1 ≤ x) (hQ : 0 ≤ Q)
    (hT1 : 1 ≤ T) (hL : 1 ≤ L) (hJ : (J : ℝ) ≤ 3 * L)
    (hTJ : T * (2 : ℝ) ^ J ≤ 2 * x / T) :
    (∑ j ∈ Finset.range J, (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * (T * (2 : ℝ) ^ j))
        + Q * x / Real.sqrt (T * (2 : ℝ) ^ j) + Q ^ 2 * Real.sqrt x))
      ≤ 32 * L * (x + Q * Real.sqrt x * T + Q * x / Real.sqrt T + Q ^ 2 * Real.sqrt x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hsqTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsqTnn : 0 ≤ Real.sqrt T := le_of_lt hsqTpos
  have hsqxnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hLnn : 0 ≤ L := le_trans zero_le_one hL
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hTJ' : T * (T * (2 : ℝ) ^ J) ≤ 2 * x := by
    have h := mul_le_mul_of_nonneg_left hTJ hT0.le
    rwa [mul_div_cancel₀ (2 * x) (ne_of_gt hT0)] at h
  set R : ℝ := x + Q * Real.sqrt x * T + Q * x / Real.sqrt T + Q ^ 2 * Real.sqrt x with hR
  set B : ℝ := Real.sqrt 2 * x + Real.sqrt 2 * Q * (x / Real.sqrt T) + Q * x / Real.sqrt T
    + Q ^ 2 * Real.sqrt x with hBdef
  have hterm : ∀ j ∈ Finset.range J,
      (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * (T * (2 : ℝ) ^ j))
        + Q * x / Real.sqrt (T * (2 : ℝ) ^ j) + Q ^ 2 * Real.sqrt x) ≤ B := by
    intro j hj
    have hjlt : j < J := Finset.mem_range.mp hj
    have hpow : 2 * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := by
      have h1 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      simpa [pow_succ, mul_comm] using h1
    have hT2j : T ^ 2 * (2 : ℝ) ^ j ≤ x := by
      have h2 : T ^ 2 * (2 * (2 : ℝ) ^ j) ≤ T ^ 2 * (2 : ℝ) ^ J :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have h3 : T ^ 2 * (2 : ℝ) ^ J ≤ 2 * x := by nlinarith [hTJ']
      nlinarith [h2, h3]
    have hle : T * (2 : ℝ) ^ j ≤ x / T := by
      rw [le_div_iff₀ hT0]
      nlinarith [hT2j]
    have hpj1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hTle : T ≤ T * (2 : ℝ) ^ j := by
      have := mul_le_mul_of_nonneg_left hpj1 hT0.le
      simpa using this
    have harg : x * (T * (2 : ℝ) ^ j) ≤ (x / Real.sqrt T) ^ 2 := by
      have hsq : (x / Real.sqrt T) ^ 2 = x ^ 2 / T := by
        rw [div_pow, Real.sq_sqrt hT0.le]
      rw [hsq, le_div_iff₀ hT0]
      have hxT2j : x * (T ^ 2 * (2 : ℝ) ^ j) ≤ x * x := mul_le_mul_of_nonneg_left hT2j hx0.le
      nlinarith [hxT2j]
    have hs1 : Real.sqrt (x * (T * (2 : ℝ) ^ j)) ≤ x / Real.sqrt T := by
      have h := Real.sqrt_le_sqrt harg
      rwa [Real.sqrt_sq (div_nonneg hx0.le hsqTnn)] at h
    have hC : Q * x / Real.sqrt (T * (2 : ℝ) ^ j) ≤ Q * x / Real.sqrt T :=
      div_le_div_of_nonneg_left (mul_nonneg hQ hx0.le) hsqTpos (Real.sqrt_le_sqrt hTle)
    have hb : Real.sqrt 2 * Q * Real.sqrt (x * (T * (2 : ℝ) ^ j))
        ≤ Real.sqrt 2 * Q * (x / Real.sqrt T) :=
      mul_le_mul_of_nonneg_left hs1 (mul_nonneg (Real.sqrt_nonneg 2) hQ)
    rw [hBdef]
    linarith [hb, hC]
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ Real.sqrt 2 * x := mul_nonneg (Real.sqrt_nonneg 2) hx0.le
    have h2 : 0 ≤ Real.sqrt 2 * Q * (x / Real.sqrt T) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hQ) (div_nonneg hx0.le hsqTnn)
    have h3 : 0 ≤ Q * x / Real.sqrt T := div_nonneg (mul_nonneg hQ hx0.le) hsqTnn
    have h4 : 0 ≤ Q ^ 2 * Real.sqrt x := mul_nonneg (sq_nonneg Q) hsqxnn
    linarith
  have hB3R : B ≤ 3 * R := by
    rw [hBdef, hR, mul_div_assoc Q x (Real.sqrt T)]
    have h1 : Real.sqrt 2 * x ≤ 2 * x := mul_le_mul_of_nonneg_right hsqrt2 hx0.le
    have hQxTnn : 0 ≤ Q * (x / Real.sqrt T) := mul_nonneg hQ (div_nonneg hx0.le hsqTnn)
    have h2 : Real.sqrt 2 * (Q * (x / Real.sqrt T)) ≤ 2 * (Q * (x / Real.sqrt T)) :=
      mul_le_mul_of_nonneg_right hsqrt2 hQxTnn
    have h4 : 0 ≤ Q ^ 2 * Real.sqrt x := mul_nonneg (sq_nonneg Q) hsqxnn
    have h5 : 0 ≤ Q * Real.sqrt x * T := by positivity
    nlinarith [h1, h2, h4, h5, hx0.le, hQxTnn]
  have hRnn : 0 ≤ R := by
    rw [hR]
    have h3 : 0 ≤ Q * x / Real.sqrt T := div_nonneg (mul_nonneg hQ hx0.le) hsqTnn
    have h4 : 0 ≤ Q ^ 2 * Real.sqrt x := mul_nonneg (sq_nonneg Q) hsqxnn
    have h5 : 0 ≤ Q * Real.sqrt x * T := by positivity
    nlinarith [hx0.le, h3, h4, h5]
  have hLR : 0 ≤ L * R := mul_nonneg hLnn hRnn
  calc
    (∑ j ∈ Finset.range J, (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * (T * (2 : ℝ) ^ j))
        + Q * x / Real.sqrt (T * (2 : ℝ) ^ j) + Q ^ 2 * Real.sqrt x))
        ≤ ∑ _j ∈ Finset.range J, B := Finset.sum_le_sum hterm
    _ = (J : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (3 * L) * B := mul_le_mul_of_nonneg_right hJ hBnn
    _ ≤ (3 * L) * (3 * R) := mul_le_mul_of_nonneg_left hB3R (by linarith)
    _ = 9 * (L * R) := by ring
    _ ≤ 32 * (L * R) := mul_le_mul_of_nonneg_right (by norm_num) hLR
    _ = 32 * L * R := by ring

end Commons.NumberTheory.BombieriVinogradov