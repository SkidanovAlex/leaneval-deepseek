import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open scoped Interval
open MeasureTheory intervalIntegral
open Polynomial

namespace Commons.Analysis.Integral

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-! ## The certificate polynomials and the master polynomial identity -/

/-- `R(s,t) = 1 + st + s²t²`. -/
private def Rf (s t : ℝ) : ℝ := 1 + s*t + s^2*t^2

/-- `W(s,t) = st(1-s³)(1-t³)`. -/
private def Wf (s t : ℝ) : ℝ := s*t*(1-s^3)*(1-t^3)

private def Hnp (N s t : ℝ) : ℝ :=
  9*(N+1)^2*(Wf s t)^2 - (10*N^2+10*N+3)*(Wf s t)*(Rf s t)^2 + N^2*(Rf s t)^4

/-- Certificate polynomial `P₀`. -/
private def P0p (s t : ℝ) : ℝ :=
  3*s^8*t^4/2 - 3*s^8*t/2 - 3*s^7*t^6 + 3*s^7*t^3 - 3*s^5*t^4 + 3*s^5*t
    + 6*s^4*t^6 - 6*s^4*t^3 + 3*s^2*t^4/2 - 3*s^2*t/2 - 3*s*t^6 + 3*s*t^3

/-- Certificate polynomial `P₁`. -/
private def P1p (s t : ℝ) : ℝ :=
  2*s^8*t^4 - 3*s^8*t/2 - 4*s^7*t^6 + 4*s^7*t^3 + s^7 + 3*s^6*t^2/2
    - 7*s^5*t^4/2 + 4*s^5*t + 8*s^4*t^6 - 7*s^4*t^3 - 3*s^4/2 - 3*s^3*t^2/2
    + 3*s^2*t^4/2 - 5*s^2*t/2 - 4*s*t^6 + 3*s*t^3 + s/2

/-- The parametric certificate polynomial `P(n) = P₀ + n·P₁`. -/
private def Pp (s t n : ℝ) : ℝ := P0p s t + n * P1p s t

/-- `∂P/∂s`. -/
private def dPp (s t n : ℝ) : ℝ :=
  12*s^7*t^4 - 12*s^7*t - 21*s^6*t^6 + 21*s^6*t^3 - 15*s^4*t^4 + 15*s^4*t
    + 24*s^3*t^6 - 24*s^3*t^3 + 3*s*t^4 - 3*s*t - 3*t^6 + 3*t^3
  + n*(16*s^7*t^4 - 12*s^7*t - 28*s^6*t^6 + 28*s^6*t^3 + 7*s^6 + 9*s^5*t^2
    - 35*s^4*t^4/2 + 20*s^4*t + 32*s^3*t^6 - 28*s^3*t^3 - 6*s^3 - 9*s^2*t^2/2
    + 3*s*t^4 - 5*s*t - 4*t^6 + 3*t^3 + 1/2)

/-- The master polynomial identity (⋆⋆). -/
private lemma starstar (s t n : ℝ) :
    Rf s t *
      ((n-1) * (Pp s t n * (4*s^3*t^4 - 4*s^3*t - t^4 + t)
                + Pp t s n * (4*s^4*t^3 - s^4 - 4*s*t^3 + s))
       + Wf s t * (dPp s t n + dPp t s n))
    - (2*n+2) * Wf s t * (Pp s t n * (2*s*t^2 + t) + Pp t s n * (2*s^2*t + s))
    = Wf s t * Hnp n s t := by
  simp only [Rf, Wf, Hnp, Pp, P0p, P1p, dPp]
  norm_num
  ring

/-- The `n = 1` instance of `⋆⋆` after dividing by `W`. -/
private lemma starstar_one (s t : ℝ) :
    Rf s t * (dPp s t 1 + dPp t s 1)
      - 4 * (Pp s t 1 * (2*s*t^2 + t) + Pp t s 1 * (2*s^2*t + s))
    = Hnp 1 s t := by
  simp only [Rf, Wf, Hnp, Pp, P0p, P1p, dPp]
  norm_num
  ring

/-! ## Polynomial (univariate in `s`, coefficients in `t`) versions, for derivatives -/

private def pPp (t n : ℝ) : Polynomial ℝ :=
  C ((3*t^4/2 - 3*t/2) + n*(2*t^4 - 3*t/2)) * X^8
  + C ((-3*t^6 + 3*t^3) + n*(-4*t^6 + 4*t^3 + 1)) * X^7
  + C (n*(3*t^2/2)) * X^6
  + C ((-3*t^4 + 3*t) + n*(-7*t^4/2 + 4*t)) * X^5
  + C ((6*t^6 - 6*t^3) + n*(8*t^6 - 7*t^3 - 3/2)) * X^4
  + C (n*(-3*t^2/2)) * X^3
  + C ((3*t^4/2 - 3*t/2) + n*(3*t^4/2 - 5*t/2)) * X^2
  + C ((-3*t^6 + 3*t^3) + n*(-4*t^6 + 3*t^3 + 1/2)) * X

private lemma Pp_eq_eval (s t n : ℝ) : Pp s t n = (pPp t n).eval s := by
  simp only [Pp, P0p, P1p, pPp, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

private lemma dPp_eq_eval (s t n : ℝ) : dPp s t n = (pPp t n).derivative.eval s := by
  simp only [dPp, pPp, derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_X_pow, derivative_C_mul_X_pow, eval_add, eval_mul, eval_C,
    eval_X, eval_pow, zero_mul, add_zero, mul_one, zero_add, one_mul]
  ring

/-- `∂P/∂s = dP`, proved via the polynomial model. -/
private lemma deriv_Pp_s (s t n : ℝ) : deriv (fun s => Pp s t n) s = dPp s t n := by
  have h : (fun s => Pp s t n) = (fun s => (pPp t n).eval s) := by
    funext s; exact Pp_eq_eval s t n
  rw [h, (Polynomial.hasDerivAt (pPp t n) s).deriv]
  exact (dPp_eq_eval s t n).symm

/-! ## Derivatives of `Rf`, `Wf` -/

private def pRf (t : ℝ) : Polynomial ℝ := C 1 + C t * X + C (t^2) * X^2
private def pWf (t : ℝ) : Polynomial ℝ := C (t*(1-t^3)) * X - C (t*(1-t^3)) * X^4

private lemma deriv_Rf_s (s t : ℝ) : deriv (fun s => Rf s t) s = 2*s*t^2 + t := by
  have h : (fun s : ℝ => Rf s t) = (fun s : ℝ => (pRf t).eval s) := by
    funext s; unfold pRf; unfold Rf
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
    try ring
  rw [h, (Polynomial.hasDerivAt (pRf t) s).deriv]
  unfold pRf
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
    derivative_C_mul_X_pow, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one,
    zero_mul, mul_one, zero_add, one_mul, mul_zero, add_zero]
  try ring

private lemma deriv_Rf_t (s t : ℝ) : deriv (fun t => Rf s t) t = 2*s^2*t + s := by
  have h : (fun t : ℝ => Rf s t) = (fun t : ℝ => (pRf s).eval t) := by
    funext t; unfold pRf; unfold Rf
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
    try ring
  rw [h, (Polynomial.hasDerivAt (pRf s) t).deriv]
  unfold pRf
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
    derivative_C_mul_X_pow, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one,
    zero_mul, mul_one, zero_add, one_mul, mul_zero, add_zero]
  try ring

private lemma deriv_Wf_s (s t : ℝ) :
    deriv (fun s => Wf s t) s = 4*s^3*t^4 - 4*s^3*t - t^4 + t := by
  have h : (fun s : ℝ => Wf s t) = (fun s : ℝ => (pWf t).eval s) := by
    funext x; unfold pWf; unfold Wf
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_neg,
      sub_eq_add_neg]
    try ring
  rw [h, (Polynomial.hasDerivAt (pWf t) s).deriv]
  unfold pWf
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
    derivative_C_mul_X_pow, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_neg,
    zero_mul, mul_one, zero_add, one_mul, mul_zero, sub_zero]
  try ring

private lemma deriv_Wf_t (s t : ℝ) :
    deriv (fun t => Wf s t) t = 4*s^4*t^3 - s^4 - 4*s*t^3 + s := by
  have h : (fun t : ℝ => Wf s t) = (fun t : ℝ => (pWf s).eval t) := by
    funext x; unfold pWf; unfold Wf
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_neg,
      sub_eq_add_neg]
    try ring
  rw [h, (Polynomial.hasDerivAt (pWf s) t).deriv]
  unfold pWf
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
    derivative_C_mul_X_pow, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_neg,
    zero_mul, mul_one, zero_add, one_mul, mul_zero, sub_zero]
  try ring

/-! ## The divergence certificate -/

private def Kf (m : ℕ) (s t : ℝ) : ℝ :=
  9^m * s^m * t^m * (1-s^3)^m * (1-t^3)^m / Rf s t^(2*m+1)

private def An (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Wf s t^(n-1) * Pp s t (n:ℝ)) / Rf s t^(2*n+2)

private def Bn (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Wf s t^(n-1) * Pp t s (n:ℝ)) / Rf s t^(2*n+2)

private def DAn (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Rf s t * deriv (fun s => Wf s t^(n-1) * Pp s t (n:ℝ)) s
      - (Wf s t^(n-1) * Pp s t (n:ℝ)) * ((2*(n:ℝ)+2)*(2*s*t^2+t)))

private def DBn (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Rf s t * deriv (fun t => Wf s t^(n-1) * Pp t s (n:ℝ)) t
      - (Wf s t^(n-1) * Pp t s (n:ℝ)) * ((2*(n:ℝ)+2)*(2*s^2*t+s)))



private def Phin (n : ℕ) (s t : ℝ) : ℝ :=
  (((n+1:ℕ):ℝ))^2 * Kf (n+1) s t - (10*(n:ℝ)^2+10*(n:ℝ)+3) * Kf n s t
    + 9*(n:ℝ)^2 * Kf (n-1) s t

private lemma Rf_pos (s t : ℝ) : 0 < Rf s t := by
  unfold Rf
  nlinarith [sq_nonneg (s*t + 1/2)]

private lemma Rf_ne (s t : ℝ) : Rf s t ≠ 0 := ne_of_gt (Rf_pos s t)

/-! ### Expanding `Phin` -/

private lemma Kf_eq (m : ℕ) (s t : ℝ) :
    Kf m s t = 9^m * (Wf s t)^m / Rf s t^(2*m+1) := by
  unfold Kf Wf
  simp only [mul_pow]
  ring

private lemma diff_Wf_s (t : ℝ) (s : ℝ) : DifferentiableAt ℝ (fun s => Wf s t) s := by
  unfold Wf; fun_prop
private lemma diff_Wf_t (s : ℝ) (t : ℝ) : DifferentiableAt ℝ (fun t => Wf s t) t := by
  unfold Wf; fun_prop
private lemma diff_Pp_s (t n : ℝ) (s : ℝ) : DifferentiableAt ℝ (fun s => Pp s t n) s := by
  unfold Pp P0p P1p; fun_prop

private lemma Phin_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    Phin n s t = 9^n * (Wf s t)^(n-1) * Hnp (n:ℝ) s t / Rf s t^(2*n+3) := by
  unfold Phin Hnp
  rw [Kf_eq (n+1), Kf_eq n, Kf_eq (n-1)]
  have hW1 : (Wf s t)^(n+1) = (Wf s t)^(n-1) * (Wf s t)^2 := by
    conv_lhs => rw [show n+1 = (n-1)+2 by omega]
    rw [pow_add]
  have hW2 : (Wf s t)^n = (Wf s t)^(n-1) * (Wf s t) := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_add, pow_one]
  have h9a : (9:ℝ)^(n+1) = 9^n * 9 := by rw [pow_succ]
  have h9c : (9:ℝ)^(n-1) = 9^n / 9 := by
    rw [eq_div_iff (by norm_num : (9:ℝ) ≠ 0)]
    conv_rhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  have hR1 : Rf s t^(2*(n+1)+1) = Rf s t^(2*n+3) := by
    rw [show 2*(n+1)+1 = 2*n+3 by omega]
  have hR2 : Rf s t^(2*n+1) = Rf s t^(2*n+3) / Rf s t^2 := by
    rw [eq_div_iff (pow_ne_zero 2 (Rf_ne s t)), ← pow_add,
      show 2*n+1+2 = 2*n+3 by omega]
  have hR3 : Rf s t^(2*(n-1)+1) = Rf s t^(2*n+3) / Rf s t^4 := by
    rw [eq_div_iff (pow_ne_zero 4 (Rf_ne s t)), ← pow_add,
      show 2*(n-1)+1+4 = 2*n+3 by omega]
  rw [hW1, hW2, h9a, h9c, hR1, hR2, hR3]
  have hR : Rf s t ≠ 0 := Rf_ne s t
  field_simp
  push_cast
  ring

private lemma cast_pred (n : ℕ) (hn : 1 ≤ n) : ((n-1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
  rw [Nat.cast_sub hn]; norm_num

private lemma deriv_U1 (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun s => Wf s t^(n-1) * Pp s t (n:ℝ)) s
      = (n-1) * (Wf s t)^(n-2) * (4*s^3*t^4 - 4*s^3*t - t^4 + t) * Pp s t (n:ℝ)
        + (Wf s t)^(n-1) * dPp s t (n:ℝ) := by
  have h1 : DifferentiableAt ℝ (fun s => Wf s t ^ (n-1)) s := by unfold Wf; fun_prop
  have h2 : DifferentiableAt ℝ (fun s => Pp s t (n:ℝ)) s := by unfold Pp P0p P1p; fun_prop
  have h3 : DifferentiableAt ℝ (fun s => Wf s t) s := by unfold Wf; fun_prop
  change deriv ((fun s => Wf s t ^ (n-1)) * (fun s => Pp s t (n:ℝ))) s
      = (n-1) * (Wf s t)^(n-2) * (4*s^3*t^4 - 4*s^3*t - t^4 + t) * Pp s t (n:ℝ)
        + (Wf s t)^(n-1) * dPp s t (n:ℝ)
  rw [deriv_mul h1 h2]
  rw [deriv_fun_pow h3, deriv_Wf_s, deriv_Pp_s]
  rw [show (n-1) - 1 = n-2 by omega]
  rw [cast_pred n hn]
  try ring

private lemma deriv_U2 (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun t => Wf s t^(n-1) * Pp t s (n:ℝ)) t
      = (n-1) * (Wf s t)^(n-2) * (4*s^4*t^3 - s^4 - 4*s*t^3 + s) * Pp t s (n:ℝ)
        + (Wf s t)^(n-1) * dPp t s (n:ℝ) := by
  have h1 : DifferentiableAt ℝ (fun t => Wf s t ^ (n-1)) t := by unfold Wf; fun_prop
  have h2 : DifferentiableAt ℝ (fun t => Pp t s (n:ℝ)) t := by unfold Pp P0p P1p; fun_prop
  have h3 : DifferentiableAt ℝ (fun t => Wf s t) t := by unfold Wf; fun_prop
  change deriv ((fun t => Wf s t ^ (n-1)) * (fun t => Pp t s (n:ℝ))) t
      = (n-1) * (Wf s t)^(n-2) * (4*s^4*t^3 - s^4 - 4*s*t^3 + s) * Pp t s (n:ℝ)
        + (Wf s t)^(n-1) * dPp t s (n:ℝ)
  rw [deriv_mul h1 h2]
  rw [deriv_fun_pow h3, deriv_Wf_t]
  have hp : deriv (fun t => Pp t s (n:ℝ)) t = dPp t s (n:ℝ) := deriv_Pp_s t s (n:ℝ)
  rw [hp]
  rw [show (n-1) - 1 = n-2 by omega]
  rw [cast_pred n hn]
  try ring

private lemma Dsum_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    DAn n s t + DBn n s t = 9^n *
      (Rf s t * ((n-1) * (Wf s t)^(n-2) * ((4*s^3*t^4-4*s^3*t-t^4+t) * Pp s t (n:ℝ)
                  + (4*s^4*t^3-s^4-4*s*t^3+s) * Pp t s (n:ℝ))
                + (Wf s t)^(n-1) * (dPp s t (n:ℝ) + dPp t s (n:ℝ)))
       - ((2:ℝ)*(n:ℝ)+2) * (Wf s t)^(n-1)
          * (Pp s t (n:ℝ)*(2*s*t^2+t) + Pp t s (n:ℝ)*(2*s^2*t+s))) := by
  unfold DAn DBn
  rw [deriv_U1 n hn, deriv_U2 n hn]
  ring

private lemma bracket_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    Rf s t * ((n-1) * (Wf s t)^(n-2) * ((4*s^3*t^4-4*s^3*t-t^4+t) * Pp s t (n:ℝ)
                + (4*s^4*t^3-s^4-4*s*t^3+s) * Pp t s (n:ℝ))
              + (Wf s t)^(n-1) * (dPp s t (n:ℝ) + dPp t s (n:ℝ)))
     - ((2:ℝ)*(n:ℝ)+2) * (Wf s t)^(n-1)
        * (Pp s t (n:ℝ)*(2*s*t^2+t) + Pp t s (n:ℝ)*(2*s^2*t+s))
    = (Wf s t)^(n-1) * Hnp (n:ℝ) s t := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    norm_num
    linear_combination starstar_one s t
  · have hss := starstar s t (n:ℝ)
    have hW : (Wf s t)^(n-1) = (Wf s t)^(n-2) * (Wf s t) := by
      rw [show n-1 = (n-2)+1 by omega, pow_succ]
    have hcast2 : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := cast_pred n hn
    simp only [hW, hcast2]
    linear_combination (Wf s t)^(n-2) * hss

private lemma numer_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    DAn n s t + DBn n s t = 9^n * (Wf s t)^(n-1) * Hnp (n:ℝ) s t := by
  rw [Dsum_eq n hn, bracket_eq n hn s t]
  ring

private lemma deriv_An (n : ℕ) (s t : ℝ) :
    deriv (fun s => An n s t) s = DAn n s t / Rf s t^(2*n+3) := by
  have hc : DifferentiableAt ℝ (fun s => 9^n * (Wf s t^(n-1) * Pp s t (n:ℝ))) s := by
    unfold Wf Pp P0p P1p; fun_prop
  have hd : DifferentiableAt ℝ (fun s => Rf s t^(2*n+2)) s := by unfold Rf; fun_prop
  have hdd : DifferentiableAt ℝ (fun s => Wf s t^(n-1) * Pp s t (n:ℝ)) s := by
    unfold Wf Pp P0p P1p; fun_prop
  unfold An DAn
  change deriv ((fun s => 9^n * (Wf s t^(n-1) * Pp s t (n:ℝ))) / (fun s => Rf s t^(2*n+2))) s
      = 9^n * (Rf s t * deriv (fun s => Wf s t^(n-1) * Pp s t (n:ℝ)) s
          - (Wf s t^(n-1) * Pp s t (n:ℝ)) * ((2*(n:ℝ)+2)*(2*s*t^2+t))) / Rf s t^(2*n+3)
  rw [deriv_div hc hd (pow_ne_zero _ (Rf_ne s t))]
  rw [deriv_const_mul _ hdd]
  rw [deriv_fun_pow (by unfold Rf; fun_prop)]
  rw [show (2*n+2)-1 = 2*n+1 by omega, deriv_Rf_s]
  have he1 : (Rf s t ^ (2*n+2))^2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Rf_ne s t))
  have he2 : Rf s t ^ (2*n+3) ≠ 0 := pow_ne_zero _ (Rf_ne s t)
  rw [div_eq_div_iff he1 he2]
  push_cast
  ring

private lemma deriv_Bn (n : ℕ) (s t : ℝ) :
    deriv (fun t => Bn n s t) t = DBn n s t / Rf s t^(2*n+3) := by
  have hc : DifferentiableAt ℝ (fun t => 9^n * (Wf s t^(n-1) * Pp t s (n:ℝ))) t := by
    unfold Wf Pp P0p P1p; fun_prop
  have hd : DifferentiableAt ℝ (fun t => Rf s t^(2*n+2)) t := by unfold Rf; fun_prop
  have hdd : DifferentiableAt ℝ (fun t => Wf s t^(n-1) * Pp t s (n:ℝ)) t := by
    unfold Wf Pp P0p P1p; fun_prop
  unfold Bn DBn
  change deriv ((fun t => 9^n * (Wf s t^(n-1) * Pp t s (n:ℝ))) / (fun t => Rf s t^(2*n+2))) t
      = 9^n * (Rf s t * deriv (fun t => Wf s t^(n-1) * Pp t s (n:ℝ)) t
          - (Wf s t^(n-1) * Pp t s (n:ℝ)) * ((2*(n:ℝ)+2)*(2*s^2*t+s))) / Rf s t^(2*n+3)
  rw [deriv_div hc hd (pow_ne_zero _ (Rf_ne s t))]
  rw [deriv_const_mul _ hdd]
  rw [deriv_fun_pow (by unfold Rf; fun_prop)]
  rw [show (2*n+2)-1 = 2*n+1 by omega, deriv_Rf_t]
  have he1 : (Rf s t ^ (2*n+2))^2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Rf_ne s t))
  have he2 : Rf s t ^ (2*n+3) ≠ 0 := pow_ne_zero _ (Rf_ne s t)
  rw [div_eq_div_iff he1 he2]
  push_cast
  ring

/-- The pointwise divergence identity. -/
private lemma deriv_identity (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun s => An n s t) s + deriv (fun t => Bn n s t) t = Phin n s t := by
  rw [deriv_An, deriv_Bn, Phin_eq n hn]
  rw [← add_div]
  congr 1
  exact numer_eq n hn s t


/-! ## Boundary vanishing of the certificate -/

private lemma Wf_zero_s (t : ℝ) : Wf 0 t = 0 := by simp [Wf]
private lemma Wf_one_s (t : ℝ) : Wf 1 t = 0 := by simp [Wf]
private lemma Wf_zero_t (s : ℝ) : Wf s 0 = 0 := by simp [Wf]
private lemma Wf_one_t (s : ℝ) : Wf s 1 = 0 := by simp [Wf]

private lemma Pp_zero_s (t n : ℝ) : Pp 0 t n = 0 := by simp [Pp, P0p, P1p]
private lemma Pp_one_s (t n : ℝ) : Pp 1 t n = 0 := by unfold Pp P0p P1p; ring

private lemma An_zero (n : ℕ) (t : ℝ) : An n 0 t = 0 := by
  unfold An; rw [Wf_zero_s, Pp_zero_s]; simp
private lemma An_one (n : ℕ) (t : ℝ) : An n 1 t = 0 := by
  unfold An; rw [Wf_one_s, Pp_one_s]; simp
private lemma Bn_zero (n : ℕ) (s : ℝ) : Bn n s 0 = 0 := by
  unfold Bn; rw [Wf_zero_t, Pp_zero_s]; simp
private lemma Bn_one (n : ℕ) (s : ℝ) : Bn n s 1 = 0 := by
  unfold Bn; rw [Wf_one_t, Pp_one_s]; simp

private lemma contDiffOn_An_s (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ContDiffOn ℝ 1 (fun s => An n s t) (Set.Icc (0:ℝ) 1) := by
  unfold An Wf Rf Pp P0p P1p
  refine ContDiffOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro s hs; exact pow_ne_zero _ (ne_of_gt (by nlinarith [sq_nonneg (s*t + 1/2)]))

private lemma contDiffOn_Bn_t (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    ContDiffOn ℝ 1 (fun t => Bn n s t) (Set.Icc (0:ℝ) 1) := by
  unfold Bn Wf Rf Pp P0p P1p
  refine ContDiffOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro t ht; exact pow_ne_zero _ (ne_of_gt (by nlinarith [sq_nonneg (s*t + 1/2)]))

/-- `∫₀¹ ∂_s An = An 1 t - An 0 t = 0`. -/
private lemma int_deriv_An (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (∫ s in (0:ℝ)..1, deriv (fun s => An n s t) s) = 0 := by
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc (contDiffOn_An_s n hn t) zero_le_one,
    An_one, An_zero, sub_zero]

/-- `∫₀¹ ∂_t Bn = Bn s 1 - Bn s 0 = 0`. -/
private lemma int_deriv_Bn (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    (∫ t in (0:ℝ)..1, deriv (fun t => Bn n s t) t) = 0 := by
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc (contDiffOn_Bn_t n hn s) zero_le_one,
    Bn_one, Bn_zero, sub_zero]

private def DAnP (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Rf s t * ((n-1) * (Wf s t)^(n-2) * (4*s^3*t^4 - 4*s^3*t - t^4 + t) * Pp s t (n:ℝ)
          + (Wf s t)^(n-1) * dPp s t (n:ℝ))
        - (Wf s t)^(n-1) * Pp s t (n:ℝ) * ((2*(n:ℝ)+2)*(2*s*t^2+t)))

private lemma DAn_eq_P (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) : DAn n s t = DAnP n s t := by
  unfold DAn DAnP
  rw [deriv_U1 n hn]

private lemma gen_deriv_An (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun s => An n s t) s = DAnP n s t / Rf s t^(2*n+3) := by
  rw [deriv_An, DAn_eq_P n hn]

private def DBnP (n : ℕ) (s t : ℝ) : ℝ :=
  9^n * (Rf s t * ((n-1) * (Wf s t)^(n-2) * (4*s^4*t^3 - s^4 - 4*s*t^3 + s) * Pp t s (n:ℝ)
          + (Wf s t)^(n-1) * dPp t s (n:ℝ))
        - (Wf s t)^(n-1) * Pp t s (n:ℝ) * ((2*(n:ℝ)+2)*(2*s^2*t+s)))

private lemma DBn_eq_P (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) : DBn n s t = DBnP n s t := by
  unfold DBn DBnP
  rw [deriv_U2 n hn]

private lemma gen_deriv_Bn (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun t => Bn n s t) t = DBnP n s t / Rf s t^(2*n+3) := by
  rw [deriv_Bn, DBn_eq_P n hn]

private lemma cont_derivAn_t (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    Continuous (fun t => deriv (fun s => An n s t) s) := by
  have h : (fun t => deriv (fun s => An n s t) s)
      = fun t => DAnP n s t / Rf s t^(2*n+3) := by
    funext t; exact gen_deriv_An n hn s t
  rw [h]
  refine Continuous.div ?_ ?_ ?_
  · unfold DAnP Wf Rf Pp P0p P1p dPp; fun_prop
  · unfold Rf; fun_prop
  · intro t; exact pow_ne_zero _ (Rf_ne s t)

private lemma cont_derivBn_t (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    Continuous (fun t => deriv (fun t => Bn n s t) t) := by
  have h : (fun t => deriv (fun t => Bn n s t) t)
      = fun t => DBnP n s t / Rf s t^(2*n+3) := by
    funext t; exact gen_deriv_Bn n hn s t
  rw [h]
  refine Continuous.div ?_ ?_ ?_
  · unfold DBnP Wf Rf Pp P0p P1p dPp; fun_prop
  · unfold Rf; fun_prop
  · intro t; exact pow_ne_zero _ (Rf_ne s t)

private lemma contOn_derivAn_rect (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => An n s p.2) p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := by
  have h : (fun p : ℝ × ℝ => deriv (fun s => An n s p.2) p.1)
      = fun p : ℝ × ℝ => DAnP n p.1 p.2 / Rf p.1 p.2^(2*n+3) := by
    funext p; exact gen_deriv_An n hn p.1 p.2
  rw [h]
  refine ContinuousOn.div ?_ ?_ ?_
  · unfold DAnP Wf Rf Pp P0p P1p dPp; fun_prop
  · unfold Rf; fun_prop
  · intro p hp; exact pow_ne_zero _ (Rf_ne p.1 p.2)

private lemma integrableOn_derivAn (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun p : ℝ × ℝ => deriv (fun s => An n s p.2) p.1)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => deriv (fun s => An n s p.2) p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :=
    (contOn_derivAn_rect n hn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine h1.mono_set ?_
  intro p hp
  simp only [Set.uIoc_of_le zero_le_one] at hp
  exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, le_of_lt hp.2.1, hp.2.2⟩

private lemma integral_Phin (n : ℕ) (hn : 1 ≤ n) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Phin n s t) = 0 := by
  have hpt : ∀ s t, Phin n s t
      = deriv (fun s => An n s t) s + deriv (fun t => Bn n s t) t :=
    fun s t => (deriv_identity n hn s t).symm
  have hA : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, deriv (fun s => An n s t) s) = 0 := by
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun s t => deriv (fun s => An n s t) s) (integrableOn_derivAn n hn)]
    simp_rw [int_deriv_An n hn]
    simp
  have hinner : ∀ s : ℝ,
      (∫ t in (0:ℝ)..1, (deriv (fun s => An n s t) s + deriv (fun t => Bn n s t) t))
        = (∫ t in (0:ℝ)..1, deriv (fun s => An n s t) s) := by
    intro s
    rw [intervalIntegral.integral_add ((cont_derivAn_t n hn s).intervalIntegrable 0 1)
      ((cont_derivBn_t n hn s).intervalIntegrable 0 1), int_deriv_Bn n hn s, add_zero]
  simp_rw [hpt, hinner]
  exact hA


private lemma cont_Kf (m : ℕ) : Continuous (Function.uncurry (Kf m)) := by
  change Continuous (fun p : ℝ × ℝ => Kf m p.1 p.2)
  simp only [Kf, Wf, Rf]
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro p; exact pow_ne_zero _ (ne_of_gt (by nlinarith [sq_nonneg (p.1*p.2 + 1/2)]))

private lemma intervalIntegrable_const_mul_Kf (m : ℕ) (s c : ℝ) :
    IntervalIntegrable (fun t => c * Kf m s t) volume (0:ℝ) 1 := by
  apply Continuous.intervalIntegrable
  exact continuous_const.mul ((cont_Kf m).comp (continuous_const.prodMk continuous_id))

private lemma intervalIntegrable_sub_const_mul_Kf (m₁ m₂ : ℕ) (s c₁ c₂ : ℝ) :
    IntervalIntegrable (fun t => c₁ * Kf m₁ s t - c₂ * Kf m₂ s t) volume (0:ℝ) 1 :=
  (intervalIntegrable_const_mul_Kf m₁ s c₁).sub (intervalIntegrable_const_mul_Kf m₂ s c₂)

private lemma continuous_paramKf (m : ℕ) :
    Continuous (fun s => ∫ t in (0:ℝ)..1, Kf m s t) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (cont_Kf m) 0 1

private lemma intervalIntegrable_const_mul_paramKf (m : ℕ) (c : ℝ) :
    IntervalIntegrable (fun s => c * ∫ t in (0:ℝ)..1, Kf m s t) volume (0:ℝ) 1 :=
  (continuous_const.mul (continuous_paramKf m)).intervalIntegrable _ _

private lemma intervalIntegrable_sub_const_mul_paramKf (m₁ m₂ : ℕ) (c₁ c₂ : ℝ) :
    IntervalIntegrable (fun s => c₁ * (∫ t in (0:ℝ)..1, Kf m₁ s t)
      - c₂ * (∫ t in (0:ℝ)..1, Kf m₂ s t)) volume (0:ℝ) 1 :=
  (intervalIntegrable_const_mul_paramKf m₁ c₁).sub (intervalIntegrable_const_mul_paramKf m₂ c₂)

/-- Linearity of the double integral over the three `Kf` summands. -/
private lemma integral_Phin_linear (n : ℕ) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Phin n s t)
      = ((((n+1:ℕ):ℝ)^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n+1) s t)
          - (10*(n:ℝ)^2+10*(n:ℝ)+3) * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf n s t))
          + 9*(n:ℝ)^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n-1) s t)) := by
  have hinner : ∀ s : ℝ, (∫ t in (0:ℝ)..1, Phin n s t)
      = ((((n+1:ℕ):ℝ)^2 * (∫ t in (0:ℝ)..1, Kf (n+1) s t)
          - (10*(n:ℝ)^2+10*(n:ℝ)+3) * (∫ t in (0:ℝ)..1, Kf n s t))
          + 9*(n:ℝ)^2 * (∫ t in (0:ℝ)..1, Kf (n-1) s t)) := by
    intro s
    simp only [Phin]
    rw [intervalIntegral.integral_add (intervalIntegrable_sub_const_mul_Kf (n+1) n s _ _)
        (intervalIntegrable_const_mul_Kf (n-1) s _),
      intervalIntegral.integral_sub (intervalIntegrable_const_mul_Kf (n+1) s _)
        (intervalIntegrable_const_mul_Kf n s _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have houter : (∫ s in (0:ℝ)..1,
      ((((n+1:ℕ):ℝ)^2 * (∫ t in (0:ℝ)..1, Kf (n+1) s t)
          - (10*(n:ℝ)^2+10*(n:ℝ)+3) * (∫ t in (0:ℝ)..1, Kf n s t))
          + 9*(n:ℝ)^2 * (∫ t in (0:ℝ)..1, Kf (n-1) s t)))
      = ((((n+1:ℕ):ℝ)^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n+1) s t)
          - (10*(n:ℝ)^2+10*(n:ℝ)+3) * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf n s t))
          + 9*(n:ℝ)^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n-1) s t)) := by
    rw [intervalIntegral.integral_add (intervalIntegrable_sub_const_mul_paramKf (n+1) n _ _)
        (intervalIntegrable_const_mul_paramKf (n-1) _),
      intervalIntegral.integral_sub (intervalIntegrable_const_mul_paramKf (n+1) _)
        (intervalIntegrable_const_mul_paramKf n _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  exact houter

/-- The requested recurrence. -/
theorem cintegral_recurrence_parametric :
    ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ) : ℝ)) ^ 2 *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
           (9:ℝ)^(n+1) * s^(n+1) * t^(n+1) * (1 - s^3)^(n+1) * (1 - t^3)^(n+1) /
             (1 + s*t + s^2*t^2)^(2*(n+1)+1))
      = (10 * (((n : ℕ) : ℝ))^2 + 10 * (((n : ℕ) : ℝ)) + 3) *
          (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
             (9:ℝ)^n * s^n * t^n * (1 - s^3)^n * (1 - t^3)^n / (1 + s*t + s^2*t^2)^(2*n+1))
        - 9 * (((n : ℕ) : ℝ))^2 *
          (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
             (9:ℝ)^(n-1) * s^(n-1) * t^(n-1) * (1 - s^3)^(n-1) * (1 - t^3)^(n-1) /
               (1 + s*t + s^2*t^2)^(2*(n-1)+1)) := by
  intro n hn
  have h0 := integral_Phin n hn
  rw [integral_Phin_linear n] at h0
  have e1 : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        (9:ℝ)^(n+1) * s^(n+1) * t^(n+1) * (1 - s^3)^(n+1) * (1 - t^3)^(n+1) /
          (1 + s*t + s^2*t^2)^(2*(n+1)+1))
      = (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n+1) s t) := by
    apply intervalIntegral.integral_congr; intro s hs
    apply intervalIntegral.integral_congr; intro t ht
    simp only [Kf, Rf]
  have e2 : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        (9:ℝ)^n * s^n * t^n * (1 - s^3)^n * (1 - t^3)^n / (1 + s*t + s^2*t^2)^(2*n+1))
      = (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf n s t) := by
    apply intervalIntegral.integral_congr; intro s hs
    apply intervalIntegral.integral_congr; intro t ht
    simp only [Kf, Rf]
  have e3 : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        (9:ℝ)^(n-1) * s^(n-1) * t^(n-1) * (1 - s^3)^(n-1) * (1 - t^3)^(n-1) /
          (1 + s*t + s^2*t^2)^(2*(n-1)+1))
      = (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, Kf (n-1) s t) := by
    apply intervalIntegral.integral_congr; intro s hs
    apply intervalIntegral.integral_congr; intro t ht
    simp only [Kf, Rf]
  rw [e1, e2, e3]
  linarith [h0]

end Commons.Analysis.Integral