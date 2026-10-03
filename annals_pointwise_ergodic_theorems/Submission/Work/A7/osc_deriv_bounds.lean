/-
# Derivative bounds for the oscillatory phase `e(ξ₁t + ξ₂P(t))` (Area A7)

This module proves `Work.A7.osc_deriv_bounds`, the pointwise `C²`/derivative estimate for the
oscillatory phase

  `f(t) = e(ξ₁ t + ξ₂ P(t)) = exp(2πi (ξ₁ t + ξ₂ P(t)))`

(`e = ee`) of the §6 model approximation of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Ann. of Math. 195 (3) 2022, under the frequency
window constraints

  `|ξ₁| ≤ 2^{k₁+1}/N`,  `|ξ₂| ≤ 2^{d(k₂+1)}/N^d`   (`d = P.natDegree`).

The two estimates are

  `‖f'(t)‖ ≤ C (2^{k₁}+2^{dk₂})/N`,  `‖f''(t)‖ ≤ C ((2^{k₁}+2^{dk₂})/N)²`  for `t ∈ [-1, N+1]`.

The route is the exact chain rule: with the real phase `φ t = ξ₁t + ξ₂P(t)`, `f = exp ∘ (2πi φ)`,
so `f' = f · 2πi φ'` and `f'' = f · ((2πi φ')² + 2πi φ'')` with `φ' = ξ₁ + ξ₂P'`, `φ'' = ξ₂P''`.
Everything therefore reduces to the elementary polynomial growth bounds

  `|P'(t)| ≤ K₁ (max 1 |t|)^{e₁}`, `|P''(t)| ≤ K₂ (max 1 |t|)^{e₂}`

(`Kᵢ` = sum of the absolute values of the coefficients, `eᵢ` = `natDegree`) for `t ∈ [-1, N+1]`,
together with `(max 1 |t|) ≤ 3N`, `e₁ + 1 ≤ d`, `e₂ + 2 ≤ d` and the arithmetic lemmas
`mul_pow_div_le`, `mul_pow_div_le_sq`.
-/
import Mathlib
import Submission.Work.A7.poly_eval_abs_le_coeffSum
import Submission.Work.A7.momFun_deriv_formula
import Submission.Work.A7.mul_pow_div_le
import Submission.Work.A7.mul_pow_div_le_sq

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7

noncomputable section

open Polynomial Finset
open scoped BigOperators

/-! ## The coefficient sum of a real polynomial -/

/-- The sum of the absolute values of the coefficients of a real polynomial. -/
noncomputable def coeffAbsSum (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

lemma coeffAbsSum_nonneg (p : Polynomial ℝ) : 0 ≤ coeffAbsSum p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-! ## The constants multiplying `(2^{k₁}+2^{dk₂})/N` and its square -/

/-- The constant of the first-derivative bound. -/
noncomputable def oscB1 (P : Polynomial ℤ) : ℝ :=
  2 * Real.pi * (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
      * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))

/-- The constant of the second-derivative bound. -/
noncomputable def oscB2 (P : Polynomial ℤ) : ℝ :=
  oscB1 P ^ 2 + 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
      * (2 : ℝ) ^ P.natDegree
      * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree))

/-! ## Degree bookkeeping for the derivatives of `P` -/

lemma natDegree_map_derivative_le (P : Polynomial ℤ) :
    (P.derivative.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree - 1 :=
  Polynomial.natDegree_map_le.trans (Polynomial.natDegree_derivative_le P)

lemma natDegree_map_derivative2_le (P : Polynomial ℤ) :
    (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree - 2 := by
  refine Polynomial.natDegree_map_le.trans ?_
  have h := Polynomial.natDegree_iterate_derivative P 2
  rwa [Function.iterate_succ_apply', Function.iterate_one] at h

lemma derivative_map_eq_zero_of_natDegree_eq_zero (P : Polynomial ℤ) (h : P.natDegree = 0) :
    P.derivative.map (Int.castRingHom ℝ) = 0 := by
  rw [Polynomial.derivative_eq_zero.mpr h, Polynomial.map_zero]

lemma derivative2_map_eq_zero_of_natDegree_le_one (P : Polynomial ℤ) (h : P.natDegree ≤ 1) :
    P.derivative.derivative.map (Int.castRingHom ℝ) = 0 := by
  have h2 : P.derivative.derivative = 0 := by
    have hh := Polynomial.iterate_derivative_eq_zero (p := P) (x := 2) (by omega)
    rwa [Function.iterate_succ_apply', Function.iterate_one] at hh
  rw [h2, Polynomial.map_zero]

lemma PderivR_eq_zero_of_natDegree_eq_zero (P : Polynomial ℤ) (h : P.natDegree = 0) (t : ℝ) :
    Work.KMTPlan.A6.PderivR P t = 0 := by
  simp [Work.KMTPlan.A6.PderivR, derivative_map_eq_zero_of_natDegree_eq_zero P h]

lemma Pderiv2R_eq_zero_of_natDegree_le_one (P : Polynomial ℤ) (h : P.natDegree ≤ 1) (t : ℝ) :
    Work.KMTPlan.A6.Pderiv2R P t = 0 := by
  simp [Work.KMTPlan.A6.Pderiv2R, derivative2_map_eq_zero_of_natDegree_le_one P h]

/-! ## Polynomial evaluation bounds -/

lemma PderivR_abs_le (P : Polynomial ℤ) (t : ℝ) :
    |Work.KMTPlan.A6.PderivR P t| ≤ coeffAbsSum (P.derivative.map (Int.castRingHom ℝ))
        * (max 1 |t|) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree) := by
  have h := poly_eval_abs_le_coeffSum (P.derivative.map (Int.castRingHom ℝ)) t
  simpa [coeffAbsSum, Work.KMTPlan.A6.PderivR] using h

lemma Pderiv2R_abs_le (P : Polynomial ℤ) (t : ℝ) :
    |Work.KMTPlan.A6.Pderiv2R P t|
      ≤ coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
        * (max 1 |t|) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree) := by
  have h := poly_eval_abs_le_coeffSum (P.derivative.derivative.map (Int.castRingHom ℝ)) t
  simpa [coeffAbsSum, Work.KMTPlan.A6.Pderiv2R] using h

/-! ## Complex norm bookkeeping -/

lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

lemma norm_two_pi_I_mul (z : ℂ) : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * z‖
    = 2 * Real.pi * ‖z‖ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  rw [show ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi by
    rw [norm_ofReal_eq_abs, abs_of_pos Real.pi_pos]]

/-! ## The `ξ₂ P'(t)` and `ξ₂ P''(t)` estimates -/

/-- **The `ξ₂ P'(t)` term.**  Under the frequency window `|ξ₂| ≤ 2^{d(k₂+1)}/N^d` and for
`t ∈ [-1, N+1]` with `N ≥ 1`,
`|ξ₂ P'(t)| ≤ K₁ 2^d 3^{e₁} (2^{k₁}+2^{dk₂})/N`, where `K₁` is the coefficient sum of `P'` and
`e₁ = natDegree P'`. -/
lemma abs_mul_PderivR_le (P : Polynomial ℤ) (k₁ : ℕ) {N k₂ : ℕ} {ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree)
          * Sval P k₁ k₂ / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  by_cases hd : P.natDegree = 0
  · have hP' : Work.KMTPlan.A6.PderivR P t = 0 := PderivR_eq_zero_of_natDegree_eq_zero P hd t
    have hK : coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) = 0 := by
      rw [derivative_map_eq_zero_of_natDegree_eq_zero P hd]
      simp [coeffAbsSum]
    rw [hP', abs_zero, mul_zero, hK]
    simp
  · have hd1 : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hd
    set e := (P.derivative.map (Int.castRingHom ℝ)).natDegree with he
    set K1 := coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) with hK1
    have hK1nn : 0 ≤ K1 := by rw [hK1]; exact coeffAbsSum_nonneg _
    have he1 : e + 1 ≤ P.natDegree := by
      have h := natDegree_map_derivative_le P
      rw [he]; omega
    have hM1 : 1 ≤ max 1 |t| := le_max_left _ _
    have hM3 : max 1 |t| ≤ 3 * N := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have ht1 : t ≤ (N : ℝ) + 1 := ht.2
      have ht0 : (-1 : ℝ) ≤ t := ht.1
      have h3 : |t| ≤ (N : ℝ) + 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have h4 : max 1 |t| ≤ (N : ℝ) + 1 := max_le (by linarith) h3
      linarith
    have hP' : |Work.KMTPlan.A6.PderivR P t| ≤ K1 * (max 1 |t|) ^ e := by
      have h := PderivR_abs_le P t
      rwa [← he, ← hK1] at h
    have hA : 0 ≤ (2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1 :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK1nn
    have hstep : ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
          * (max 1 |t|) ^ e / (N : ℝ) ^ P.natDegree
        ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
          * (3 : ℝ) ^ e / (N : ℝ) :=
      mul_pow_div_le hN hM1 hM3 hA he1
    have hSk₂ : (2 : ℝ) ^ (P.natDegree * k₂) ≤ Sval P k₁ k₂ := by
      have h := le_add_of_nonneg_left (a := (2 : ℝ) ^ (P.natDegree * k₂)) (b := (2 : ℝ) ^ k₁)
        (show (0 : ℝ) ≤ (2 : ℝ) ^ k₁ by positivity)
      simpa [Sval] using h
    have hZ : 0 ≤ K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e :=
      mul_nonneg (mul_nonneg hK1nn (by positivity)) (by positivity)
    calc |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
        ≤ ((2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
            * (K1 * (max 1 |t|) ^ e) :=
          mul_le_mul hξ₂ hP' (abs_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
            * (max 1 |t|) ^ e / (N : ℝ) ^ P.natDegree := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
            * (3 : ℝ) ^ e / (N : ℝ) := hstep
      _ ≤ K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e * Sval P k₁ k₂ / (N : ℝ) := by
          rw [show ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1) * (3 : ℝ) ^ e
                = (K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e)
                    * (2 : ℝ) ^ (P.natDegree * k₂) by ring]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSk₂ hZ) hN0

/-- **The `ξ₂ P''(t)` term.**  Under the frequency window `|ξ₂| ≤ 2^{d(k₂+1)}/N^d` and for
`t ∈ [-1, N+1]` with `N ≥ 1`,
`|ξ₂ P''(t)| ≤ K₂ 2^d 3^{e₂} ((2^{k₁}+2^{dk₂})/N)²`, where `K₂` is the coefficient sum of `P''` and
`e₂ = natDegree P''`. -/
lemma abs_mul_Pderiv2R_le (P : Polynomial ℤ) (k₁ : ℕ) {N k₂ : ℕ} {ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
      ≤ coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree)
          * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  by_cases hd : P.natDegree ≤ 1
  · have hP' : Work.KMTPlan.A6.Pderiv2R P t = 0 := Pderiv2R_eq_zero_of_natDegree_le_one P hd t
    have hK : coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) = 0 := by
      rw [derivative2_map_eq_zero_of_natDegree_le_one P hd]
      simp [coeffAbsSum]
    rw [hP', abs_zero, mul_zero, hK]
    simp
  · have hd2 : 2 ≤ P.natDegree := by omega
    set e2 := (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree with he2
    set K2 := coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) with hK2
    have hK2nn : 0 ≤ K2 := by rw [hK2]; exact coeffAbsSum_nonneg _
    have he2' : e2 + 2 ≤ P.natDegree := by
      have h := natDegree_map_derivative2_le P
      rw [he2]; omega
    have hM1 : 1 ≤ max 1 |t| := le_max_left _ _
    have hM3 : max 1 |t| ≤ 3 * N := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have ht1 : t ≤ (N : ℝ) + 1 := ht.2
      have ht0 : (-1 : ℝ) ≤ t := ht.1
      have h3 : |t| ≤ (N : ℝ) + 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have h4 : max 1 |t| ≤ (N : ℝ) + 1 := max_le (by linarith) h3
      linarith
    have hP' : |Work.KMTPlan.A6.Pderiv2R P t| ≤ K2 * (max 1 |t|) ^ e2 := by
      have h := Pderiv2R_abs_le P t
      rwa [← he2, ← hK2] at h
    have hA : 0 ≤ (2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2 :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK2nn
    have hstep : ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
          * (max 1 |t|) ^ e2 / (N : ℝ) ^ P.natDegree
        ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
          * (3 : ℝ) ^ e2 / (N : ℝ) ^ 2 :=
      mul_pow_div_le_sq hN hM1 hM3 hA he2'
    have hS1 : 1 ≤ Sval P k₁ k₂ := by
      have h : (1 : ℝ) ≤ (2 : ℝ) ^ k₁ := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) := by positivity
      rw [Sval]; linarith
    have hSk₂ : (2 : ℝ) ^ (P.natDegree * k₂) ≤ Sval P k₁ k₂ := by
      have h := le_add_of_nonneg_left (a := (2 : ℝ) ^ (P.natDegree * k₂)) (b := (2 : ℝ) ^ k₁)
        (show (0 : ℝ) ≤ (2 : ℝ) ^ k₁ by positivity)
      simpa [Sval] using h
    have hSk₂2 : (2 : ℝ) ^ (P.natDegree * k₂) ≤ (Sval P k₁ k₂) ^ 2 :=
      le_trans hSk₂ (le_self_pow₀ hS1 (by norm_num))
    have hZ : 0 ≤ K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2 :=
      mul_nonneg (mul_nonneg hK2nn (by positivity)) (by positivity)
    calc |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
        ≤ ((2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
            * (K2 * (max 1 |t|) ^ e2) :=
          mul_le_mul hξ₂ hP' (abs_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
            * (max 1 |t|) ^ e2 / (N : ℝ) ^ P.natDegree := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
            * (3 : ℝ) ^ e2 / (N : ℝ) ^ 2 := hstep
      _ ≤ K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2 * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
          rw [show ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2) * (3 : ℝ) ^ e2
                = (K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2)
                    * (2 : ℝ) ^ (P.natDegree * k₂) by ring]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSk₂2 hZ) (by positivity)

/-! ## The derivative bounds for the phase -/

/-- **The linear part of the derivative of the phase.** -/
lemma phase_deriv_bound (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₁ ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))
          * Sval P k₁ k₂ / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hSk₁ : (2 : ℝ) ^ k₁ ≤ Sval P k₁ k₂ := by
    have h := le_add_of_nonneg_right (a := (2 : ℝ) ^ k₁)
      (show (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) by positivity)
    simpa [Sval] using h
  have hξ₁' : |ξ₁| ≤ 2 * Sval P k₁ k₂ / (N : ℝ) := by
    calc |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) := hξ₁
      _ = 2 * (2 : ℝ) ^ k₁ / (N : ℝ) := by rw [pow_succ]; ring
      _ ≤ 2 * Sval P k₁ k₂ / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith [hSk₁]) hN0
  have hP' := abs_mul_PderivR_le P k₁ hN hξ₂ ht
  calc |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ 2 * Sval P k₁ k₂ / (N : ℝ)
        + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree) * Sval P k₁ k₂
          / (N : ℝ) :=
        add_le_add hξ₁' hP'
    _ = (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree)) * Sval P k₁ k₂
          / (N : ℝ) := by ring

/-- **The first-derivative bound.** -/
lemma norm_deriv_momFun_le (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₁ ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    ‖deriv (momFun P ξ₁ ξ₂) t‖ ≤ oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
  rw [momFun_deriv_formula]
  rw [norm_mul, norm_two_pi_I_mul, momFun_norm_eq_one, one_mul]
  have hc : ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      ≤ |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
    calc ‖(ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖
        ≤ ‖(ξ₁ : ℂ)‖ + ‖(ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
          simp [norm_mul]
  have hpd := phase_deriv_bound P hN hξ₁ hξ₂ ht
  have hmain : 2 * Real.pi
        * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      ≤ oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
    calc 2 * Real.pi
          * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
        ≤ 2 * Real.pi * (|ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2 * Real.pi * ((2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ))
              * (2 : ℝ) ^ P.natDegree
              * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))
            * Sval P k₁ k₂ / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hpd (by positivity)
      _ = oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
          unfold oscB1; ring
  exact hmain

/-! ## The target -/

end

end Work.A7
