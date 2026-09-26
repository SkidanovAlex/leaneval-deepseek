/-
# Bound on the iterated derivatives of the complex Gaussian `s ↦ exp(-(a s²))`

This file proves the elementary estimate behind the seminorm bounds of the CKMRV `low` layer:
for every order `m` there is an (explicit) constant `C m` with

  `‖iteratedDeriv m (fun s : ℝ => Complex.exp (-(a * s ^ 2))) r‖
     ≤ C m * (1 + ‖a‖) ^ (2 * m) * (1 + |r|) ^ m * Real.exp (-(a.re) * r ^ 2)`

for every complex parameter `a` and every `r : ℝ`.  The constant is super-exponential in `m`
(the true derivatives grow like factorials, e.g. at `a = 1`, `r = 0` and `m = 2k` the value is
`(2k)!/k!`), and the statement records the admissible value `C m = (m+1) * (m+2)!`.

The proof writes `iteratedDeriv m (fun s => exp(-(a s²))) s = P_m(s) * exp(-(a s²))` with the
polynomials `P_m` defined by the (Hermite-like) recursion `P_0 = 1`,
`P_{m+1} = P_m' - 2a X P_m`, and bounds the coefficients of `P_m` by induction.
-/
import Mathlib

noncomputable section

open scoped Topology
open Polynomial

namespace Work.Asymptotics

/-- The polynomials `P_m` attached to the parameter `a : ℂ`: `P_0 = 1` and
`P_{m+1} = P_m' - 2a X P_m`, so that
`iteratedDeriv m (fun s => Complex.exp (-(a * s^2))) s = (P_m).eval s * Complex.exp (-(a * s^2))`. -/
noncomputable def gaussPoly (a : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | (m + 1) =>
      (gaussPoly a m).derivative - Polynomial.C (2 * a) * (Polynomial.X * (gaussPoly a m))

@[simp] lemma gaussPoly_zero (a : ℂ) : gaussPoly a 0 = 1 := rfl

@[simp] lemma gaussPoly_succ (a : ℂ) (m : ℕ) :
    gaussPoly a (m + 1)
      = (gaussPoly a m).derivative
          - Polynomial.C (2 * a) * (Polynomial.X * (gaussPoly a m)) := rfl

/-- `deriv (fun x : ℝ => (x : ℂ)) s = 1`. -/
lemma deriv_ofReal_eq_one (s : ℝ) : deriv (fun x : ℝ => (x : ℂ)) s = 1 := by
  simpa using ((hasDerivAt_id s).ofReal_comp).deriv

/-- The derivative of the complex Gaussian `s ↦ exp(-(a s²))`. -/
lemma deriv_gaussExp (a : ℂ) (s : ℝ) :
    deriv (fun x : ℝ => Complex.exp (-(a * (x : ℂ) ^ 2))) s
      = Complex.exp (-(a * (s : ℂ) ^ 2)) * (-(a * (2 * (s : ℂ)))) := by
  rw [deriv_cexp (by fun_prop)]
  congr 1
  have h2 : deriv (fun x : ℝ => (-a) * (x : ℂ) ^ 2) s = (-a) * (2 * (s : ℂ)) := by
    rw [deriv_const_mul _ (by fun_prop),
      show (fun x : ℝ => (x : ℂ) ^ 2) = (fun x : ℝ => (x : ℂ)) ^ 2 from rfl,
      deriv_pow (by fun_prop), deriv_ofReal_eq_one]
    ring
  rw [show (fun x : ℝ => -(a * (x : ℂ) ^ 2)) = fun x : ℝ => (-a) * (x : ℂ) ^ 2 from by
    funext x; ring, h2]
  ring

/-- The key identity: the `m`-th derivative of the Gaussian is `P_m` times the Gaussian. -/
lemma iteratedDeriv_gaussPoly (a : ℂ) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2)))
      = fun s : ℝ => (gaussPoly a m).eval (s : ℂ) * Complex.exp (-(a * (s : ℂ) ^ 2)) := by
  induction m with
  | zero => funext s; simp
  | succ m ih =>
    funext s
    rw [iteratedDeriv_succ, ih]
    have hE : deriv (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) s
        = Complex.exp (-(a * (s : ℂ) ^ 2)) * (-(a * (2 * (s : ℂ)))) := deriv_gaussExp a s
    have hp_hasAt : HasDerivAt (fun s : ℝ => (gaussPoly a m).eval (s : ℂ))
        ((gaussPoly a m).derivative.eval (s : ℂ)) s :=
      ((gaussPoly a m).hasDerivAt (s : ℂ)).comp_ofReal
    have hp : deriv (fun s : ℝ => (gaussPoly a m).eval (s : ℂ)) s
        = (gaussPoly a m).derivative.eval (s : ℂ) := hp_hasAt.deriv
    have hd1 : DifferentiableAt ℝ (fun s : ℝ => (gaussPoly a m).eval (s : ℂ)) s :=
      hp_hasAt.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) s := by
      fun_prop
    have hmain : deriv (fun s : ℝ => (gaussPoly a m).eval (s : ℂ) *
          Complex.exp (-(a * (s : ℂ) ^ 2))) s
        = (gaussPoly a (m + 1)).eval (s : ℂ) * Complex.exp (-(a * (s : ℂ) ^ 2)) := by
      rw [show (fun s : ℝ => (gaussPoly a m).eval (s : ℂ) * Complex.exp (-(a * (s : ℂ) ^ 2)))
          = (fun s : ℝ => (gaussPoly a m).eval (s : ℂ)) *
            (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) from rfl]
      rw [deriv_mul hd1 hd2, hp, hE, gaussPoly_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    exact hmain

/-! ## Coefficient bounds -/

/-- The coefficient-growth constant `E m = (m+2)!/2`. -/
def gaussC (m : ℕ) : ℝ := ((m + 2).factorial : ℝ) / 2

lemma gaussC_pos (m : ℕ) : 0 < gaussC m := by
  rw [gaussC]; positivity

lemma gaussC_nonneg (m : ℕ) : 0 ≤ gaussC m := (gaussC_pos m).le

lemma gaussC_succ (m : ℕ) : gaussC (m + 1) = (m + 3) * gaussC m := by
  rw [gaussC, gaussC, Nat.factorial_succ]
  push_cast
  ring

lemma gaussC_mono (m : ℕ) : gaussC m ≤ gaussC (m + 1) := by
  rw [gaussC_succ]
  have h : (1 : ℝ) ≤ (m : ℝ) + 3 := by
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; linarith
  nlinarith [gaussC_pos m]

lemma gaussC_le_factorial (m : ℕ) : gaussC m ≤ ((m + 2).factorial : ℝ) := by
  rw [gaussC]
  have h : (0:ℝ) < ((m+2).factorial : ℝ) := by positivity
  linarith

/-- Degree and (uniform) coefficient bounds for `gaussPoly`, proved simultaneously. -/
lemma gaussPoly_deg_and_coeff (a : ℂ) :
    ∀ m, (gaussPoly a m).natDegree ≤ m ∧
      ∀ k, ‖(gaussPoly a m).coeff k‖ ≤ gaussC m * (1 + ‖a‖) ^ (2 * m) := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp, ?_⟩
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [gaussC]
    · rw [gaussPoly_zero, Polynomial.coeff_one, if_neg (by omega), norm_zero]
      exact mul_nonneg (gaussC_nonneg _) (pow_nonneg (by positivity) _)
  | succ m ih =>
    obtain ⟨hdeg, hcoeff⟩ := ih
    set A : ℝ := 1 + ‖a‖ with hA
    have hA1 : (1 : ℝ) ≤ A := by rw [hA]; linarith [norm_nonneg a]
    have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
    have hAnn : ∀ n : ℕ, (0 : ℝ) ≤ A ^ n := fun n => pow_nonneg hA0.le n
    have hβ : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    constructor
    · rw [gaussPoly_succ]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_derivative_le _) ?_
        omega
      · have h1 : (Polynomial.C (2 * a) * (Polynomial.X * (gaussPoly a m))).natDegree
            ≤ (Polynomial.C (2 * a)).natDegree
              + (Polynomial.X * (gaussPoly a m)).natDegree := Polynomial.natDegree_mul_le
        have h2 : (Polynomial.X * (gaussPoly a m)).natDegree ≤ 1 + (gaussPoly a m).natDegree :=
          le_trans Polynomial.natDegree_mul_le (add_le_add Polynomial.natDegree_X_le le_rfl)
        have h3 : (Polynomial.C (2 * a)).natDegree = 0 := Polynomial.natDegree_C (2 * a)
        omega
    · intro k
      rw [gaussPoly_succ, Polynomial.coeff_sub, Polynomial.coeff_derivative,
        Polynomial.coeff_C_mul]
      have hX : ‖(Polynomial.X * (gaussPoly a m)).coeff k‖ ≤ gaussC m * A ^ (2 * m) := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [Polynomial.coeff_X_mul_zero, norm_zero]
          exact mul_nonneg (gaussC_nonneg m) (hAnn (2 * m))
        · obtain ⟨k'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [Polynomial.coeff_X_mul]
          exact hcoeff k''
      by_cases hk : k ≤ m
      · have hnorm : ‖((k : ℂ) + 1)‖ = ((k : ℝ) + 1) := by
          have h : ((k:ℂ) + 1) = ((k+1 : ℕ) : ℂ) := by push_cast; ring
          rw [h, Complex.norm_natCast]; push_cast; ring
        have hknn : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
        have hderiv : ‖(gaussPoly a m).coeff (k + 1) * ((k : ℂ) + 1)‖
            ≤ ((m : ℝ) + 1) * (gaussC m * A ^ (2 * m)) := by
          rw [norm_mul, hnorm]
          calc ‖(gaussPoly a m).coeff (k + 1)‖ * ((k : ℝ) + 1)
              ≤ (gaussC m * A ^ (2 * m)) * ((k : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right (hcoeff (k + 1)) hknn
            _ ≤ (gaussC m * A ^ (2 * m)) * ((m : ℝ) + 1) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (gaussC_nonneg m) (hAnn (2 * m)))
                have : k + 1 ≤ m + 1 := by omega
                exact_mod_cast this
            _ = ((m : ℝ) + 1) * (gaussC m * A ^ (2 * m)) := by ring
        have hX' : ‖2 * a * (Polynomial.X * (gaussPoly a m)).coeff k‖
            ≤ 2 * ‖a‖ * (gaussC m * A ^ (2 * m)) := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left hX (by positivity)
        refine le_trans (norm_sub_le _ _) ?_
        refine le_trans (add_le_add hderiv hX') ?_
        have harith : ((m : ℝ) + 1 + 2 * ‖a‖) ≤ ((m : ℝ) + 3) * A ^ 2 := by
          rw [hA]; nlinarith [hβ, sq_nonneg ‖a‖]
        calc ((m : ℝ) + 1) * (gaussC m * A ^ (2 * m)) + 2 * ‖a‖ * (gaussC m * A ^ (2 * m))
            = (((m : ℝ) + 1) + 2 * ‖a‖) * (gaussC m * A ^ (2 * m)) := by ring
          _ ≤ (((m : ℝ) + 3) * A ^ 2) * (gaussC m * A ^ (2 * m)) :=
              mul_le_mul_of_nonneg_right harith (mul_nonneg (gaussC_nonneg m) (hAnn (2 * m)))
          _ = gaussC (m + 1) * A ^ (2 * (m + 1)) := by
              rw [gaussC_succ, show (2:ℕ) * (m + 1) = 2 * m + 2 by omega, pow_add]
              ring
      · have hz1 : (gaussPoly a m).coeff (k + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp only [hz1, zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_ofNat]
        calc 2 * ‖a‖ * ‖(Polynomial.X * (gaussPoly a m)).coeff k‖
            ≤ 2 * ‖a‖ * (gaussC m * A ^ (2 * m)) := by
              exact mul_le_mul_of_nonneg_left hX (by positivity)
          _ ≤ gaussC (m + 1) * A ^ (2 * (m + 1)) := by
              have harith : 2 * ‖a‖ ≤ ((m : ℝ) + 3) * A ^ 2 := by
                rw [hA]; nlinarith [hβ, sq_nonneg ‖a‖]
              rw [gaussC_succ, show (2:ℕ) * (m + 1) = 2 * m + 2 by omega, pow_add]
              have hstep := mul_le_mul_of_nonneg_right harith
                (mul_nonneg (gaussC_nonneg m) (hAnn (2 * m)))
              calc 2 * ‖a‖ * (gaussC m * A ^ (2 * m))
                  = (2 * ‖a‖) * (gaussC m * A ^ (2 * m)) := by ring
                _ ≤ (((m : ℝ) + 3) * A ^ 2) * (gaussC m * A ^ (2 * m)) := hstep
                _ = ((m : ℝ) + 3) * gaussC m * (A ^ (2 * m) * A ^ 2) := by ring

/-- Evaluation bound for the polynomials `P_m`. -/
lemma gaussPoly_eval_bound (a : ℂ) (m : ℕ) (r : ℝ) :
    ‖(gaussPoly a m).eval (r : ℂ)‖
      ≤ ((m + 1 : ℕ) : ℝ) * gaussC m * (1 + ‖a‖) ^ (2 * m) * (1 + |r|) ^ m := by
  obtain ⟨hdeg, hcoeff⟩ := gaussPoly_deg_and_coeff a m
  rw [Polynomial.eval_eq_sum_range]
  set A : ℝ := 1 + ‖a‖ with hA
  have hA1 : (1 : ℝ) ≤ A := by rw [hA]; linarith [norm_nonneg a]
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  have hAnn : ∀ n : ℕ, (0 : ℝ) ≤ A ^ n := fun n => pow_nonneg hA0.le n
  have hrn : (0 : ℝ) ≤ 1 + |r| := by positivity
  have h1 : ‖∑ i ∈ Finset.range ((gaussPoly a m).natDegree + 1),
      (gaussPoly a m).coeff i * (r : ℂ) ^ i‖
      ≤ ∑ _i ∈ Finset.range ((gaussPoly a m).natDegree + 1),
          gaussC m * A ^ (2 * m) * (1 + |r|) ^ m := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro i hi
    have hnormr : ‖((r : ℂ))‖ = |r| := RCLike.norm_ofReal r
    rw [norm_mul, Complex.norm_pow, hnormr]
    have hci := hcoeff i
    have hi_le : i ≤ m := by
      have : i < (gaussPoly a m).natDegree + 1 := Finset.mem_range.mp hi
      omega
    have hri : |r| ^ i ≤ (1 + |r|) ^ m := by
      calc |r| ^ i ≤ (1 + |r|) ^ i := pow_le_pow_left₀ (abs_nonneg r) (by linarith) i
        _ ≤ (1 + |r|) ^ m := pow_le_pow_right₀ (by have h := abs_nonneg r; linarith) hi_le
    calc ‖(gaussPoly a m).coeff i‖ * |r| ^ i
        ≤ (gaussC m * A ^ (2 * m)) * |r| ^ i :=
          mul_le_mul_of_nonneg_right hci (pow_nonneg (abs_nonneg r) i)
      _ ≤ (gaussC m * A ^ (2 * m)) * (1 + |r|) ^ m :=
          mul_le_mul_of_nonneg_left hri (mul_nonneg (gaussC_nonneg m) (hAnn (2 * m)))
      _ = gaussC m * A ^ (2 * m) * (1 + |r|) ^ m := rfl
  refine le_trans h1 ?_
  have hsum : ∑ _i ∈ Finset.range ((gaussPoly a m).natDegree + 1),
        gaussC m * A ^ (2 * m) * (1 + |r|) ^ m
      = (((gaussPoly a m).natDegree + 1 : ℕ) : ℝ)
          * (gaussC m * A ^ (2 * m) * (1 + |r|) ^ m) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  have hle : (((gaussPoly a m).natDegree + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : (gaussPoly a m).natDegree + 1 ≤ m + 1 := by omega
    exact_mod_cast this
  calc (((gaussPoly a m).natDegree + 1 : ℕ) : ℝ) * (gaussC m * A ^ (2 * m) * (1 + |r|) ^ m)
      ≤ ((m + 1 : ℕ) : ℝ) * (gaussC m * A ^ (2 * m) * (1 + |r|) ^ m) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg (gaussC_nonneg m) (hAnn (2 * m))) (pow_nonneg hrn _))
    _ = ((m + 1 : ℕ) : ℝ) * gaussC m * (1 + ‖a‖) ^ (2 * m) * (1 + |r|) ^ m := by
        rw [hA]; ring

/-- **The main estimate**: iterated derivatives of the complex Gaussian. -/
theorem iteratedDeriv_exp_neg_sq_bound :
    ∀ (m : ℕ) (a : ℂ) (r : ℝ),
      ‖iteratedDeriv m (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) r‖
        ≤ ((m + 1 : ℕ) : ℝ) * (Nat.factorial (m + 2) : ℝ) * (1 + ‖a‖) ^ (2 * m)
            * (1 + |r|) ^ m * Real.exp (-(a.re) * r ^ 2) := by
  intro m a r
  rw [iteratedDeriv_gaussPoly a m, norm_mul]
  have hE : ‖Complex.exp (-(a * (r : ℂ) ^ 2))‖ = Real.exp (-(a.re) * r ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    have hsq : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hsq, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hE]
  have hev := gaussPoly_eval_bound a m r
  have hfac : gaussC m ≤ ((m + 2).factorial : ℝ) := gaussC_le_factorial m
  have hnn : (0 : ℝ)
      ≤ ((m + 1 : ℕ) : ℝ) * (1 + ‖a‖) ^ (2 * m) * (1 + |r|) ^ m
          * Real.exp (-(a.re) * r ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfac hnn
  calc ‖(gaussPoly a m).eval (↑r)‖ * Real.exp (-(a.re) * r ^ 2)
      ≤ (((m + 1 : ℕ) : ℝ) * gaussC m * (1 + ‖a‖) ^ (2 * m) * (1 + |r|) ^ m)
          * Real.exp (-(a.re) * r ^ 2) :=
        mul_le_mul_of_nonneg_right hev (Real.exp_nonneg _)
    _ ≤ ((m + 1 : ℕ) : ℝ) * (Nat.factorial (m + 2) : ℝ) * (1 + ‖a‖) ^ (2 * m)
          * (1 + |r|) ^ m * Real.exp (-(a.re) * r ^ 2) := by
        nlinarith [hmul]

end Work.Asymptotics
