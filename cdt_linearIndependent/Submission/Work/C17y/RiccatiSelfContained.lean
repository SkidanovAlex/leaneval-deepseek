import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.riccati_degree
import Submission.Work.C17.p2x_roots_simple
import Submission.Work.C17.riccati_denom_squarefree
import Submission.Work.C17.roots_sum_div_derivative
import Submission.Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff
import Submission.Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime

/-!
# Self-contained copy of the Riccati non-existence input

This module is a **verbatim copy** of `Submission/Work/C17/riccati_no_rational.lean` (same proof,
same lemmas), re-namespaced to `Work.C17y` and with the three definitions `P2C, P1C, P0C` dropped
(they now live in the shared module `Submission.Work.C17.seventeen_defs`, which this file imports).
The main theorem is called `Work.C17y.riccati_no_rational_y` here.

**Reason for the copy.**  A concurrent refactor moved `P2C, P1C, P0C` into
`Submission.Work.C17.seventeen_defs` without removing them from
`Submission.Work.C17.riccati_no_rational`, so that module currently fails to compile
(`Work.C17.P2C has already been declared`) and cannot be imported by anyone.  Since a file of
another author must not be edited, this copy keeps `Work.C17y.poly_indep` (which needs the Riccati
non-existence statement) independent of that breakage.  Once
`Submission.Work.C17.riccati_no_rational` compiles again, the import of this module in
`Submission/Work/C17y/poly_indep.lean` can be reverted to it and this file deleted.
-/

namespace Work.C17y

open Polynomial
open Work.C17

noncomputable section

/-! ## The `ℂ`-images of the coefficients of `M` -/

def Q4C (a b : ℚ) : Polynomial ℂ := (Q4x a b).map (algebraMap ℚ ℂ)

/-! ## Elementary evaluations over `ℚ` -/

lemma Q4x_eval_zero (a b : ℚ) : (Q4x a b).eval (0 : ℚ) = 1 := by simp [Q4x]

lemma Q4x_eval_one (a b : ℚ) : (Q4x a b).eval (1 : ℚ) = 4 * (a - b) ^ 2 := by
  simp only [Q4x, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  ring

lemma Q4x_eval_neg_one (a b : ℚ) : (Q4x a b).eval (-1 : ℚ) = 4 * (a + b) ^ 2 := by
  simp only [Q4x, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  ring

lemma P1x_eval_zero (a b : ℚ) : (P1x a b).eval (0 : ℚ) = -1 := by simp [P1x]

lemma P1x_eval_one (a b : ℚ) : (P1x a b).eval (1 : ℚ) = -8 * (a - b) ^ 2 := by
  simp only [P1x, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_neg]
  ring

lemma P1x_eval_neg_one (a b : ℚ) : (P1x a b).eval (-1 : ℚ) = -8 * (a + b) ^ 2 := by
  simp only [P1x, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_neg]
  ring

lemma P0x_eval_zero (a b : ℚ) : (P0x a b).eval (0 : ℚ) = a * b := by simp [P0x]

lemma deriv_X3 : ((X - 1) * X * (X + 1) : Polynomial ℚ).derivative = 3 * X ^ 2 - 1 := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_sub,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.derivative_add]
  ring

lemma P2x_derivative_eq (a b : ℚ) :
    (P2x a b).derivative
      = (3 * X ^ 2 - 1) * Q4x a b + ((X - 1) * X * (X + 1)) * (Q4x a b).derivative := by
  rw [P2x, Polynomial.derivative_mul, deriv_X3]

lemma P2x_deriv_eval_zero (a b : ℚ) : (P2x a b).derivative.eval (0 : ℚ) = -1 := by
  rw [P2x_derivative_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_neg, Q4x,
    Polynomial.eval_ofNat]
  norm_num

lemma P2x_deriv_eval_one (a b : ℚ) : (P2x a b).derivative.eval (1 : ℚ) = 8 * (a - b) ^ 2 := by
  rw [P2x_derivative_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_neg, Q4x,
    Polynomial.eval_ofNat]
  ring

lemma P2x_deriv_eval_neg_one (a b : ℚ) : (P2x a b).derivative.eval (-1 : ℚ) = 8 * (a + b) ^ 2 := by
  rw [P2x_derivative_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_neg, Q4x,
    Polynomial.eval_ofNat]
  ring

lemma P2x_natDegree (a b : ℚ) : (P2x a b).natDegree = 7 := by
  rw [P2x, Q4x]; compute_degree!

lemma P2x_leadingCoeff (a b : ℚ) : (P2x a b).leadingCoeff = 1 := by
  rw [← Polynomial.coeff_natDegree, show (P2x a b).natDegree = 7 from P2x_natDegree a b]
  rw [P2x, Q4x]; compute_degree!

lemma P1x_natDegree (a b : ℚ) : (P1x a b).natDegree = 6 := by
  rw [P1x]; compute_degree!; norm_num [Polynomial.coeff_one]

lemma P1x_leadingCoeff (a b : ℚ) : (P1x a b).leadingCoeff = 3 := by
  rw [← Polynomial.coeff_natDegree, show (P1x a b).natDegree = 6 from P1x_natDegree a b, P1x]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  norm_num

lemma P0x_natDegree (a b : ℚ) : (P0x a b).natDegree = 5 := by
  rw [P0x]; compute_degree!

lemma P0x_leadingCoeff (a b : ℚ) : (P0x a b).leadingCoeff = 1 := by
  rw [← Polynomial.coeff_natDegree, show (P0x a b).natDegree = 5 from P0x_natDegree a b]
  rw [P0x]; compute_degree!

/-- `P₁ ≡ P₂' mod Q₄`. -/
lemma P1x_eq_deriv (a b : ℚ) :
    P1x a b = (X - 1) * X * (X + 1) * (Q4x a b).derivative - (X ^ 2 + 1) * Q4x a b := by
  apply Polynomial.funext
  intro x
  simp only [P1x, Q4x, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_one,
    Polynomial.derivative_add, Polynomial.derivative_pow]
  ring

/-! ## Transfer to `ℂ` -/

lemma eval_map_rat (p : Polynomial ℚ) (x : ℚ) :
    ((p.map (algebraMap ℚ ℂ)).eval (algebraMap ℚ ℂ x)) = algebraMap ℚ ℂ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma eval_map_rat_deriv (p : Polynomial ℚ) (x : ℚ) :
    (((p.map (algebraMap ℚ ℂ)).derivative).eval (algebraMap ℚ ℂ x))
      = algebraMap ℚ ℂ (p.derivative.eval x) := by
  rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma Q4C_eval_zero (a b : ℚ) : (Q4C a b).eval (0 : ℂ) = 1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, Q4C, eval_map_rat, Q4x_eval_zero]
  norm_num

lemma Q4C_eval_one (a b : ℚ) : (Q4C a b).eval (1 : ℂ) = 4 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, Q4C, eval_map_rat, Q4x_eval_one]
  norm_num

lemma Q4C_eval_neg_one (a b : ℚ) : (Q4C a b).eval (-1 : ℂ) = 4 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, Q4C, eval_map_rat, Q4x_eval_neg_one]
  norm_num

lemma P1C_eval_zero (a b : ℚ) : (P1C a b).eval (0 : ℂ) = -1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, P1C, eval_map_rat, P1x_eval_zero]
  norm_num

lemma P1C_eval_one (a b : ℚ) : (P1C a b).eval (1 : ℂ) = -8 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, P1C, eval_map_rat, P1x_eval_one]
  norm_num

lemma P1C_eval_neg_one (a b : ℚ) : (P1C a b).eval (-1 : ℂ) = -8 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, P1C, eval_map_rat, P1x_eval_neg_one]
  norm_num

lemma P0C_eval_zero (a b : ℚ) : (P0C a b).eval (0 : ℂ) = (a : ℂ) * (b : ℂ) := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, P0C, eval_map_rat, P0x_eval_zero]
  norm_num

lemma P2C_deriv_eval_zero (a b : ℚ) : (P2C a b).derivative.eval (0 : ℂ) = -1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, P2C, eval_map_rat_deriv,
    P2x_deriv_eval_zero]
  norm_num

lemma P2C_deriv_eval_one (a b : ℚ) :
    (P2C a b).derivative.eval (1 : ℂ) = 8 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, P2C, eval_map_rat_deriv,
    P2x_deriv_eval_one]
  norm_num

lemma P2C_deriv_eval_neg_one (a b : ℚ) :
    (P2C a b).derivative.eval (-1 : ℂ) = 8 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, P2C, eval_map_rat_deriv,
    P2x_deriv_eval_neg_one]
  norm_num

lemma P2C_natDegree (a b : ℚ) : (P2C a b).natDegree = 7 := by
  rw [P2C, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P2x_natDegree]

lemma P2C_leadingCoeff (a b : ℚ) : (P2C a b).leadingCoeff = 1 := by
  rw [P2C, Polynomial.leadingCoeff_map_of_injective (Rat.cast_injective), P2x_leadingCoeff]
  norm_num

lemma P1C_natDegree (a b : ℚ) : (P1C a b).natDegree = 6 := by
  rw [P1C, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P1x_natDegree]

lemma P1C_leadingCoeff (a b : ℚ) : (P1C a b).leadingCoeff = 3 := by
  rw [P1C, Polynomial.leadingCoeff_map_of_injective (Rat.cast_injective), P1x_leadingCoeff]
  norm_num

lemma P0C_natDegree (a b : ℚ) : (P0C a b).natDegree = 5 := by
  rw [P0C, Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective), P0x_natDegree]

lemma P0C_leadingCoeff (a b : ℚ) : (P0C a b).leadingCoeff = 1 := by
  rw [P0C, Polynomial.leadingCoeff_map_of_injective (Rat.cast_injective), P0x_leadingCoeff]
  norm_num

lemma P2C_ne_zero (a b : ℚ) : P2C a b ≠ 0 := by
  intro h
  have := P2C_natDegree a b
  rw [h] at this
  simp at this

lemma P0C_ne_zero (a b : ℚ) : P0C a b ≠ 0 := by
  intro h
  have := P0C_natDegree a b
  rw [h] at this
  simp at this

lemma P2C_coeff_seven (a b : ℚ) : (P2C a b).coeff 7 = 1 := by
  rw [← P2C_natDegree a b, Polynomial.coeff_natDegree, P2C_leadingCoeff]

lemma P1C_coeff_seven (a b : ℚ) : (P1C a b).coeff 7 = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [P1C_natDegree]; norm_num

lemma P0C_coeff_seven (a b : ℚ) : (P0C a b).coeff 7 = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [P0C_natDegree]; norm_num

lemma P2C_factor (a b : ℚ) : P2C a b = (X - 1) * X * (X + 1) * Q4C a b := by
  simp only [P2C, P2x, Q4C, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_add]

lemma P2C_deriv_eval_at_Q4_root (a b : ℚ) (β : ℂ) (h : (Q4C a b).eval β = 0) :
    (P2C a b).derivative.eval β = (β - 1) * β * (β + 1) * (Q4C a b).derivative.eval β := by
  have hlin : ((X - 1) * X * (X + 1) : Polynomial ℂ).eval β = (β - 1) * β * (β + 1) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
  rw [P2C_factor, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_mul, h, mul_zero, zero_add, hlin]

lemma P1C_eval_eq_P2C_deriv_eval (a b : ℚ) (β : ℂ) (h : (Q4C a b).eval β = 0) :
    (P1C a b).eval β = (P2C a b).derivative.eval β := by
  have hid : P1C a b = (X - 1) * X * (X + 1) * (Q4C a b).derivative - (X ^ 2 + 1) * Q4C a b := by
    have hmap := congrArg (Polynomial.map (algebraMap ℚ ℂ)) (P1x_eq_deriv a b)
    rw [P1C, Q4C, hmap]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, ← Polynomial.derivative_map]
  have hlin : ((X - 1) * X * (X + 1) : Polynomial ℂ).eval β = (β - 1) * β * (β + 1) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
  rw [hid, P2C_deriv_eval_at_Q4_root a b β h]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, h, mul_zero, hlin]
  ring

lemma Q4C_deriv_ne_zero_of_root (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) {β : ℂ}
    (h : (Q4C a b).eval β = 0) : (Q4C a b).derivative.eval β ≠ 0 := by
  intro h0
  have hsq : (X - C β) ^ 2 ∣ P2C a b := by
    rw [Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff]
    constructor
    · rw [P2C_factor]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, h, mul_zero]
    · rw [P2C_deriv_eval_at_Q4_root a b β h, h0, mul_zero]
  have hroot : Polynomial.rootMultiplicity β (P2C a b) ≤ 1 := by
    simpa only [P2C] using p2x_roots_simple a b ha hb hab β
  have h2 : 2 ≤ Polynomial.rootMultiplicity β (P2C a b) := by
    rw [Polynomial.le_rootMultiplicity_iff (P2C_ne_zero a b)]
    exact hsq
  omega

lemma Q4C_root_ne_zero (a b : ℚ) {β : ℂ} (h : (Q4C a b).eval β = 0) : β ≠ 0 := by
  intro h0
  rw [h0, Q4C_eval_zero] at h
  exact one_ne_zero h

lemma Q4C_root_ne_one (a b : ℚ) (hab : a ≠ b) {β : ℂ} (h : (Q4C a b).eval β = 0) : β ≠ 1 := by
  intro h0
  rw [h0, Q4C_eval_one] at h
  have hδ : ((a : ℂ) - (b : ℂ)) = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact sq_eq_zero_iff.mp h'
  exact hab (by exact_mod_cast (sub_eq_zero.mp hδ))

lemma Q4C_root_ne_neg_one (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) {β : ℂ}
    (h : (Q4C a b).eval β = 0) : β ≠ -1 := by
  intro h0
  rw [h0, Q4C_eval_neg_one] at h
  have hσ : ((a : ℂ) + (b : ℂ)) = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact sq_eq_zero_iff.mp h'
  have hsum : (a : ℂ) = ((-b : ℚ) : ℂ) := by
    rw [Rat.cast_neg]
    exact eq_neg_of_add_eq_zero_left hσ
  have hab' : a = -b := by exact_mod_cast hsum
  have h6 : (6 : ℚ) ≤ a + b := by linarith
  have hzero : a + b = 0 := by rw [hab']; ring
  linarith

/-! ## The two local constraints on the residue -/

lemma local_residue_eval {K : Type*} [Field K] (P2 P1 P0 A B : Polynomial K) (β : K)
    (hB : B.eval β = 0)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0) :
    P2.eval β * A.eval β * (A.eval β - B.derivative.eval β) = 0 := by
  have h2 := congrArg (Polynomial.eval β) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    hB, Polynomial.eval_zero, mul_zero, add_zero] at h2
  ring_nf at h2 ⊢
  linear_combination h2

lemma local_residue_deriv {K : Type*} [Field K] (P2 P1 P0 A B : Polynomial K) (β : K)
    (hP2 : P2.eval β = 0) (hB : B.eval β = 0)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0) :
    P2.derivative.eval β * (A.eval β) ^ 2 - P2.derivative.eval β * A.eval β * B.derivative.eval β
      + P1.eval β * A.eval β * B.derivative.eval β = 0 := by
  have h' := congrArg (fun p => Polynomial.eval β (Polynomial.derivative p)) h
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_one,
    Polynomial.derivative_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero,
    hP2, hB, mul_zero, add_zero, zero_mul, sub_zero, zero_sub] at h'
  ring_nf at h' ⊢
  linear_combination h'

/-! ## The main theorem -/

theorem riccati_no_rational_y (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) (u : RatFunc ℚ) :
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) (P2x a b)) * (Submission.CDT.dRat u + u ^ 2)
      + (algebraMap (Polynomial ℚ) (RatFunc ℚ) (P1x a b)) * u
      + (algebraMap (Polynomial ℚ) (RatFunc ℚ) (P0x a b)) ≠ 0 := by
  intro hEq
  -- ## 1. the cleared identity over `ℚ`
  have hpolyQ : P2x a b * (u.num.derivative * u.denom - u.num * u.denom.derivative)
      + P2x a b * u.num ^ 2 + P1x a b * u.num * u.denom + P0x a b * u.denom ^ 2 = 0 := by
    have hden : u.denom ≠ 0 := RatFunc.denom_ne_zero u
    have hAmap : (algebraMap (Polynomial ℚ) (RatFunc ℚ) u.denom) ≠ 0 := by simpa using hden
    have hnum : u = algebraMap (Polynomial ℚ) (RatFunc ℚ) u.num
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) u.denom := (RatFunc.num_div_denom u).symm
    have key : (algebraMap (Polynomial ℚ) (RatFunc ℚ))
        (P2x a b * (u.num.derivative * u.denom - u.num * u.denom.derivative) + P2x a b * u.num ^ 2
          + P1x a b * u.num * u.denom + P0x a b * u.denom ^ 2) = 0 := by
      rw [hnum, Submission.CDT.dRat_div] at hEq
      simp only [map_add, map_mul, map_sub, map_pow] at hEq ⊢
      field_simp at hEq ⊢
      ring_nf at hEq ⊢
      linear_combination hEq
    exact RatFunc.algebraMap_injective ℚ (by simpa using key)
  -- ## 2. base change to `ℂ`
  set A : Polynomial ℂ := u.num.map (algebraMap ℚ ℂ) with hAdef
  set B : Polynomial ℂ := u.denom.map (algebraMap ℚ ℂ) with hBdef
  have hpoly : P2C a b * (A.derivative * B - A * B.derivative) + P2C a b * A ^ 2
      + P1C a b * A * B + P0C a b * B ^ 2 = 0 := by
    rw [hAdef, hBdef]
    have h := congrArg (Polynomial.map (algebraMap ℚ ℂ)) hpolyQ
    simpa only [P2C, P1C, P0C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_zero, Polynomial.derivative_map] using h
  -- ## 3. basic properties of `A` and `B`
  have hBmonic : B.Monic := by
    rw [hBdef]
    exact (RatFunc.monic_denom u).map (algebraMap ℚ ℂ)
  have hB0 : B ≠ 0 := hBmonic.ne_zero
  have hcop : IsCoprime A B := by
    rw [hAdef, hBdef]
    exact (RatFunc.isCoprime_num_denom u).map (Polynomial.mapRingHom (algebraMap ℚ ℂ))
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0] at hpoly
    have hz : P0C a b * B ^ 2 = 0 := by simpa using hpoly
    rcases mul_eq_zero.mp hz with h | h
    · exact P0C_ne_zero a b h
    · exact hB0 (sq_eq_zero_iff.mp h)
  -- ## 4. the degree of `A` and the degree of `B`
  obtain ⟨hdegA, hleadA⟩ := riccati_degree (P2C a b) (P1C a b) (P0C a b) A B hBmonic hAne
    (P2C_natDegree a b) (P2C_leadingCoeff a b) (P1C_natDegree a b) (P1C_leadingCoeff a b)
    (P0C_natDegree a b) (P0C_leadingCoeff a b) hpoly
  have hBdeg : 1 ≤ B.natDegree := by
    by_contra hcon
    have hBnat : B.natDegree = 0 := by omega
    have hAnat : A.natDegree = 0 := by omega
    have hAcoeff : A.coeff 0 = -1 := by
      rw [← hAnat, Polynomial.coeff_natDegree]
      exact hleadA
    have hAeq : A = Polynomial.C (-1) := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hAnat, hAcoeff]
    have hBeq : B = 1 := by
      have hc : B.coeff 0 = 1 := by
        rw [← hBnat, Polynomial.coeff_natDegree]
        exact hBmonic
      rw [Polynomial.eq_C_of_natDegree_eq_zero hBnat, hc, Polynomial.C_1]
    rw [hAeq, hBeq] at hpoly
    have hred : P2C a b + P1C a b * Polynomial.C (-1) + P0C a b = 0 := by simpa using hpoly
    have h7 := congrArg (fun p : Polynomial ℂ => p.coeff 7) hred
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_mul_C, P2C_coeff_seven a b,
      P1C_coeff_seven a b, P0C_coeff_seven a b] at h7
    norm_num at h7
  -- ## 5. `B` has simple roots only
  have hrootB : ∀ α : ℂ, Polynomial.rootMultiplicity α B ≤ 1 := fun α =>
    riccati_denom_squarefree (P2C a b) (P1C a b) (P0C a b) A B hBmonic (P2C_ne_zero a b) hcop
      (fun α => by simpa only [P2C] using p2x_roots_simple a b ha hb hab α) hpoly α
  have hnodup : B.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro β
    rw [Polynomial.count_roots]
    exact hrootB β
  -- ## 6. the residue at each root of `B` is `1` or `2`
  have hres : ∀ β ∈ B.roots,
      A.eval β / B.derivative.eval β = 1 ∨ A.eval β / B.derivative.eval β = 2 := by
    intro β hβ
    have hBeval : B.eval β = 0 := Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hB0).mp hβ)
    have hB'ne : B.derivative.eval β ≠ 0 := by
      rw [Polynomial.Splits.eval_root_derivative (IsAlgClosed.splits B) hBmonic hβ]
      apply Multiset.prod_ne_zero
      rw [Multiset.mem_map]
      rintro ⟨γ, hγ, hγ0⟩
      exact (hnodup.mem_erase_iff.mp hγ).1 (sub_eq_zero.mp hγ0).symm
    have hAeval : A.eval β ≠ 0 :=
      Commons.Algebra.Polynomial.ne_zero_of_eval_eq_zero_of_isCoprime hcop.symm hBeval
    by_cases hP2β : (P2C a b).eval β = 0
    · have hconstr := local_residue_deriv (P2C a b) (P1C a b) (P0C a b) A B β hP2β hBeval hpoly
      have hprod : (β - 1) * β * (β + 1) * (Q4C a b).eval β = 0 := by
        have h := hP2β
        rw [P2C_factor] at h
        simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one] using h
      rcases mul_eq_zero.mp hprod with h1 | hQ4
      · rcases mul_eq_zero.mp h1 with h2 | hβm1
        · rcases mul_eq_zero.mp h2 with hβ1 | hβ0
          · -- `β = 1`: the residue is `2`
            have hb1 : β = 1 := sub_eq_zero.mp hβ1
            subst hb1
            right
            have hδ : ((a : ℂ) - (b : ℂ)) ≠ 0 := by
              intro hz
              exact hab (by exact_mod_cast (sub_eq_zero.mp hz))
            rw [P2C_deriv_eval_one a b, P1C_eval_one a b] at hconstr
            have hfac : 8 * ((a : ℂ) - (b : ℂ)) ^ 2 * A.eval 1
                * (A.eval 1 - 2 * B.derivative.eval 1) = 0 := by
              linear_combination hconstr
            have hA1 : A.eval 1 = 2 * B.derivative.eval 1 := by
              have h8 : 8 * ((a : ℂ) - (b : ℂ)) ^ 2 ≠ 0 :=
                mul_ne_zero (by norm_num) (pow_ne_zero 2 hδ)
              rcases mul_eq_zero.mp hfac with h | h
              · rcases mul_eq_zero.mp h with h' | h'
                · exact absurd h' h8
                · exact absurd h' hAeval
              · exact sub_eq_zero.mp h
            rw [hA1, mul_div_assoc, div_self hB'ne, mul_one]
          · -- `β = 0`: impossible
            exfalso
            subst hβ0
            rw [P2C_deriv_eval_zero a b, P1C_eval_zero a b] at hconstr
            have hz : (A.eval 0) ^ 2 = 0 := by
              have h' : -((A.eval 0) ^ 2) = 0 := by linear_combination hconstr
              exact neg_eq_zero.mp h'
            exact hAeval (sq_eq_zero_iff.mp hz)
        · -- `β = -1`: the residue is `2`
          have hbm1 : β = -1 := eq_neg_of_add_eq_zero_left hβm1
          subst hbm1
          right
          have hσ : ((a : ℂ) + (b : ℂ)) ≠ 0 := by
            intro hz
            have hsum : (a : ℂ) = ((-b : ℚ) : ℂ) := by
              rw [Rat.cast_neg]
              exact eq_neg_of_add_eq_zero_left hz
            have hab' : a = -b := by exact_mod_cast hsum
            have h6 : (6 : ℚ) ≤ a + b := by linarith
            have hzero : a + b = 0 := by rw [hab']; ring
            linarith
          rw [P2C_deriv_eval_neg_one a b, P1C_eval_neg_one a b] at hconstr
          have hfac : 8 * ((a : ℂ) + (b : ℂ)) ^ 2 * A.eval (-1)
              * (A.eval (-1) - 2 * B.derivative.eval (-1)) = 0 := by
            linear_combination hconstr
          have hA1 : A.eval (-1) = 2 * B.derivative.eval (-1) := by
            have h8 : 8 * ((a : ℂ) + (b : ℂ)) ^ 2 ≠ 0 :=
              mul_ne_zero (by norm_num) (pow_ne_zero 2 hσ)
            rcases mul_eq_zero.mp hfac with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' h8
              · exact absurd h' hAeval
            · exact sub_eq_zero.mp h
          rw [hA1, mul_div_assoc, div_self hB'ne, mul_one]
      · -- `Q₄(β) = 0`: impossible
        exfalso
        have hp1 : (P2C a b).derivative.eval β ≠ 0 := by
          rw [P2C_deriv_eval_at_Q4_root a b β hQ4]
          refine mul_ne_zero ?_ (Q4C_deriv_ne_zero_of_root a b ha hb hab hQ4)
          refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Q4C_root_ne_one a b hab hQ4)) ?_) ?_
          · exact Q4C_root_ne_zero a b hQ4
          · intro hz
            exact Q4C_root_ne_neg_one a b ha hb hQ4 (eq_neg_of_add_eq_zero_left hz)
        have hq0 : (P1C a b).eval β = (P2C a b).derivative.eval β :=
          P1C_eval_eq_P2C_deriv_eval a b β hQ4
        rw [hq0] at hconstr
        have hz : (A.eval β) ^ 2 = 0 := by
          have h' : (P2C a b).derivative.eval β * (A.eval β) ^ 2 = 0 := by
            linear_combination hconstr
          rcases mul_eq_zero.mp h' with h | h
          · exact absurd h hp1
          · exact h
        exact hAeval (sq_eq_zero_iff.mp hz)
    · left
      have hc := local_residue_eval (P2C a b) (P1C a b) (P0C a b) A B β hBeval hpoly
      have hAB : A.eval β = B.derivative.eval β := by
        rcases mul_eq_zero.mp hc with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hP2β
          · exact absurd h' hAeval
        · exact sub_eq_zero.mp h
      rw [hAB, div_self hB'ne]
  -- ## 7. the sum of the residues
  have hdeg_lt : A.natDegree < B.natDegree := by omega
  have hsum := roots_sum_div_derivative A B hBmonic hnodup hdeg_lt
  have hcoeff : A.coeff (B.natDegree - 1) = -1 := by
    rw [← hdegA, Polynomial.coeff_natDegree]
    exact hleadA
  have hsumval : (B.roots.map (fun β => A.eval β / B.derivative.eval β)).sum = -1 := by
    rw [hsum, hcoeff]
  -- ## 8. a sum of values in `{1,2}` cannot be `-1`
  set c : ℂ → ℂ := fun β => A.eval β / B.derivative.eval β with hcdef
  have hc : ∀ β ∈ B.roots, c β = 1 ∨ c β = 2 := by
    intro β hβ
    rw [hcdef]
    exact hres β hβ
  have hsumc : (B.roots.map c).sum = -1 := by
    rw [hcdef]
    exact hsumval
  have hre : ((B.roots.map c).sum).re = ((B.roots.map c).map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom _
  have hnonneg : 0 ≤ ((B.roots.map c).map Complex.re).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hy
    rcases hc β hβ with h | h <;> simp [h]
  have hone : ((B.roots.map c).map Complex.re).sum = -1 := by
    rw [← hre, hsumc]
    norm_num
  linarith

end

end Work.C17y
