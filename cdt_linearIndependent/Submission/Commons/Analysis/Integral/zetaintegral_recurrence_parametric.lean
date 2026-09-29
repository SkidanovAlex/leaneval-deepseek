import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

open scoped ENNReal

namespace Commons.Analysis.Integral

noncomputable section

open scoped Interval
open MeasureTheory intervalIntegral Polynomial

/-! ## The divergence certificate for the ζ-side Beukers integral

We prove the Zagier (Franel) recurrence
`(n+1)²·I_{n+1} = -(7n²+7n+2)·I_n + 8n²·I_{n-1}` for
`I_n = ∫₀¹∫₀¹ (1-s²)ⁿ(1-t²)ⁿ/(1-st)^{n+1} ds dt`
by exhibiting a divergence certificate: polynomials `a, b` with

`∂_s A + ∂_t B = (n+1)² K_{n+1} + (7n²+7n+2) K_n - 8 n² K_{n-1}`,
`K_m = (1-s²)^m (1-t²)^m/(1-st)^{m+1}`,
`A = P^{n-1} a / R^{n+1}`, `B = P^{n-1} b / R^{n+1}`, `P = (1-s²)(1-t²)`, `R = 1-st`,
with `A` vanishing on `s = 0,1` and `B` vanishing on `t = 0,1`. -/

/-- `P(s,t) = (1-s²)(1-t²)`. -/
def Pz (s t : ℝ) : ℝ := (1 - s^2) * (1 - t^2)

/-- `R(s,t) = 1 - st`. -/
def Rz (s t : ℝ) : ℝ := 1 - s*t

/-- certificate polynomial `a` -/
def za (s t n : ℝ) : ℝ :=
  -(1/2) * s * (1 - s^2) *
    (n*(s^2*t^2 + s^2 + 6*s*t - t^4 + 2*t^2 - 9) + (-2*t^4 + 4*t^2 - 2))

/-- certificate polynomial `b` -/
def zb (s t n : ℝ) : ℝ :=
  (1/2) * t * (1 - t^2) *
    (n*(s^4 + 2*s^3*t - s^2*t^2 - 6*s^2 - 4*s*t - t^2 + 9) + (2*s^4 + 2*s^3*t - 6*s^2 - 2*s*t + 4))

/-- `∂_s a` -/
def zda (s t n : ℝ) : ℝ :=
  (1/2)*(5*n*s^4*t^2 + 5*n*s^4 + 24*n*s^3*t - 3*n*s^2*t^4 + 3*n*s^2*t^2 - 30*n*s^2
    - 12*n*s*t + n*t^4 - 2*n*t^2 + 9*n - 6*s^2*t^4 + 12*s^2*t^2 - 6*s^2 + 2*t^4 - 4*t^2 + 2)

/-- `∂_t b` -/
def zdb (s t n : ℝ) : ℝ :=
  -(1/2)*(3*n*s^4*t^2 - n*s^4 + 8*n*s^3*t^3 - 4*n*s^3*t - 5*n*s^2*t^4 - 15*n*s^2*t^2
    + 6*n*s^2 - 16*n*s*t^3 + 8*n*s*t - 5*n*t^4 + 30*n*t^2 - 9*n + 6*s^4*t^2 - 2*s^4
    + 8*s^3*t^3 - 4*s^3*t - 18*s^2*t^2 + 6*s^2 - 8*s*t^3 + 4*s*t + 12*t^2 - 4)

/-- `S = (n+1)²P² + (7n²+7n+2)PR - 8n²R²` -/
def zS (s t n : ℝ) : ℝ :=
  (n+1)^2*(Pz s t)^2 + (7*n^2+7*n+2)*(Pz s t)*(Rz s t) - 8*n^2*(Rz s t)^2

/-- `P` as a polynomial in `s` -/
private def pPz (t : ℝ) : Polynomial ℝ :=
  Polynomial.C 1 - Polynomial.C 1 * Polynomial.X^2 * Polynomial.C (1-t^2) * 0
    - Polynomial.C (1-t^2) * Polynomial.X^2 + Polynomial.C (1-t^2)

private def zaP (t n : ℝ) : Polynomial ℝ :=
  Polynomial.C (-(1/2)*(n*(-t^4+2*t^2-9) + (-2*t^4+4*t^2-2))) * Polynomial.X
  + Polynomial.C (-(1/2)*(6*n*t)) * Polynomial.X^2
  + Polynomial.C (-(1/2)*((n*(t^2+1)) - (n*(-t^4+2*t^2-9) + (-2*t^4+4*t^2-2)))) * Polynomial.X^3
  + Polynomial.C ((1/2)*(6*n*t)) * Polynomial.X^4
  + Polynomial.C ((1/2)*(n*(t^2+1))) * Polynomial.X^5

private def zbP (s n : ℝ) : Polynomial ℝ :=
  Polynomial.C ((1/2)*(n*(s^4-6*s^2+9)+(2*s^4-6*s^2+4))) * Polynomial.X
  + Polynomial.C ((1/2)*(2*s^3*(n+1)-2*s*(2*n+1))) * Polynomial.X^2
  + Polynomial.C ((1/2)*((-n*(1+s^2)) - (n*(s^4-6*s^2+9)+(2*s^4-6*s^2+4)))) * Polynomial.X^3
  + Polynomial.C (-(1/2)*(2*s^3*(n+1)-2*s*(2*n+1))) * Polynomial.X^4
  + Polynomial.C (-(1/2)*(-n*(1+s^2))) * Polynomial.X^5

lemma deriv_za (s t n : ℝ) : deriv (fun s : ℝ => za s t n) s = zda s t n := by
  have h : (fun s : ℝ => za s t n) = fun s : ℝ => (zaP t n).eval s := by
    funext s
    simp only [za, zaP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rw [h, (Polynomial.hasDerivAt (zaP t n) s).deriv]
  simp only [zaP, Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, zda]
  ring

lemma deriv_zb (s t n : ℝ) : deriv (fun t : ℝ => zb s t n) t = zdb s t n := by
  have h : (fun t : ℝ => zb s t n) = fun t : ℝ => (zbP s n).eval t := by
    funext t
    simp only [zb, zbP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rw [h, (Polynomial.hasDerivAt (zbP s n) t).deriv]
  simp only [zbP, Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, zdb]
  ring

/-- **The polynomial divergence certificate**: with `a = za`, `b = zb`,
`F = (n-1)∂_sP·a·R + P·∂_s a·R - (n+1)P·a·∂_sR` and the analogous `G`,
one has `F + G = P·S`. -/
private lemma zcert_poly (s t n : ℝ) :
    (n-1)*(-2*s*(1-t^2))*za s t n*(Rz s t) + (Pz s t)*zda s t n*(Rz s t)
        - (n+1)*(Pz s t)*za s t n*(-t)
      + (n-1)*(-2*t*(1-s^2))*zb s t n*(Rz s t) + (Pz s t)*zdb s t n*(Rz s t)
        - (n+1)*(Pz s t)*zb s t n*(-s)
    = Pz s t * zS s t n := by
  simp only [Pz, Rz, za, zb, zda, zdb, zS]
  ring

/-- `A = P^{n-1} a / R^{n+1}` -/
def zA (n : ℕ) (s t : ℝ) : ℝ := (Pz s t)^(n-1) * za s t (n:ℝ) / (Rz s t)^(n+1)

/-- `B = P^{n-1} b / R^{n+1}` -/
def zB (n : ℕ) (s t : ℝ) : ℝ := (Pz s t)^(n-1) * zb s t (n:ℝ) / (Rz s t)^(n+1)

/-- `R^{n+2} ∂_s A` -/
def zDAs (n : ℕ) (s t : ℝ) : ℝ :=
  ((n-1:ℝ)*(Pz s t)^(n-2)*(-2*s*(1-t^2))*za s t (n:ℝ) + (Pz s t)^(n-1)*zda s t (n:ℝ)) * Rz s t
    - (n+1:ℝ)*(Pz s t)^(n-1)*za s t (n:ℝ)*(-t)

/-- `R^{n+2} ∂_t B` -/
def zDBs (n : ℕ) (s t : ℝ) : ℝ :=
  ((n-1:ℝ)*(Pz s t)^(n-2)*(-2*t*(1-s^2))*zb s t (n:ℝ) + (Pz s t)^(n-1)*zdb s t (n:ℝ)) * Rz s t
    - (n+1:ℝ)*(Pz s t)^(n-1)*zb s t (n:ℝ)*(-s)

private lemma deriv_Pz_s (s t : ℝ) : deriv (fun s : ℝ => Pz s t) s = -2*s*(1-t^2) := by
  have h : (fun s : ℝ => Pz s t) = fun s : ℝ =>
      (Polynomial.C (1-t^2) - Polynomial.C (1-t^2) * Polynomial.X^2).eval s := by
    funext s; simp only [Pz, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]; ring
  rw [h, (Polynomial.hasDerivAt _ s).deriv]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero]
  ring

private lemma deriv_Pz_t (s t : ℝ) : deriv (fun t : ℝ => Pz s t) t = -2*t*(1-s^2) := by
  have h : (fun t : ℝ => Pz s t) = fun t : ℝ =>
      (Polynomial.C (1-s^2) - Polynomial.C (1-s^2) * Polynomial.X^2).eval t := by
    funext t; simp only [Pz, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]; ring
  rw [h, (Polynomial.hasDerivAt _ t).deriv]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero]
  ring

private lemma deriv_Rz_s (s t : ℝ) : deriv (fun s : ℝ => Rz s t) s = -t := by
  have h : (fun s : ℝ => Rz s t) = fun s : ℝ =>
      (Polynomial.C 1 - Polynomial.C t * Polynomial.X).eval s := by
    funext s; simp only [Rz, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]; ring
  rw [h, (Polynomial.hasDerivAt _ s).deriv]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  ring

private lemma deriv_Rz_t (s t : ℝ) : deriv (fun t : ℝ => Rz s t) t = -s := by
  have h : (fun t : ℝ => Rz s t) = fun t : ℝ =>
      (Polynomial.C 1 - Polynomial.C s * Polynomial.X).eval t := by
    funext t; simp only [Rz, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  rw [h, (Polynomial.hasDerivAt _ t).deriv]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  ring

private lemma deriv_U_s (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun s : ℝ => (Pz s t)^(n-1) * za s t (n:ℝ)) s
      = ((n-1:ℝ)*(Pz s t)^(n-2)*(-2*s*(1-t^2))*za s t (n:ℝ)
          + (Pz s t)^(n-1)*zda s t (n:ℝ)) := by
  have h1 : DifferentiableAt ℝ (fun s : ℝ => (Pz s t)^(n-1)) s := by unfold Pz; fun_prop
  have h2 : DifferentiableAt ℝ (fun s : ℝ => za s t (n:ℝ)) s := by unfold za; fun_prop
  change deriv ((fun s : ℝ => (Pz s t)^(n-1)) * (fun s : ℝ => za s t (n:ℝ))) s = _
  rw [deriv_mul h1 h2]
  rw [deriv_fun_pow (by unfold Pz; fun_prop), deriv_Pz_s, deriv_za]
  rw [show (n-1-1 : ℕ) = n-2 by omega, Nat.cast_sub hn, Nat.cast_one]

private lemma deriv_U_t (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    deriv (fun t : ℝ => (Pz s t)^(n-1) * zb s t (n:ℝ)) t
      = ((n-1:ℝ)*(Pz s t)^(n-2)*(-2*t*(1-s^2))*zb s t (n:ℝ)
          + (Pz s t)^(n-1)*zdb s t (n:ℝ)) := by
  have h1 : DifferentiableAt ℝ (fun t : ℝ => (Pz s t)^(n-1)) t := by unfold Pz; fun_prop
  have h2 : DifferentiableAt ℝ (fun t : ℝ => zb s t (n:ℝ)) t := by unfold zb; fun_prop
  change deriv ((fun t : ℝ => (Pz s t)^(n-1)) * (fun t : ℝ => zb s t (n:ℝ))) t = _
  rw [deriv_mul h1 h2]
  rw [deriv_fun_pow (by unfold Pz; fun_prop), deriv_Pz_t, deriv_zb]
  rw [show (n-1-1 : ℕ) = n-2 by omega, Nat.cast_sub hn, Nat.cast_one]

/-- `∂_s A` in explicit form -/
private lemma deriv_zA_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hR : Rz s t ≠ 0) :
    deriv (fun s : ℝ => zA n s t) s
      = ((((n-1:ℝ)*(Pz s t)^(n-2)*(-2*s*(1-t^2))*za s t (n:ℝ)
            + (Pz s t)^(n-1)*zda s t (n:ℝ)) * (Rz s t)^(n+1)
          - (Pz s t)^(n-1)*za s t (n:ℝ) * ((n+1:ℝ)*(Rz s t)^n*(-t)))
          / ((Rz s t)^(n+1))^2) := by
  have hU : DifferentiableAt ℝ (fun s : ℝ => (Pz s t)^(n-1) * za s t (n:ℝ)) s := by
    unfold Pz za; fun_prop
  have hD : DifferentiableAt ℝ (fun s : ℝ => (Rz s t)^(n+1)) s := by unfold Rz; fun_prop
  unfold zA
  change deriv ((fun s : ℝ => (Pz s t)^(n-1) * za s t (n:ℝ))
      / (fun s : ℝ => (Rz s t)^(n+1))) s = _
  rw [deriv_div hU hD (pow_ne_zero _ hR)]
  rw [deriv_U_s n hn, deriv_fun_pow (by unfold Rz; fun_prop), deriv_Rz_s]
  rw [show (n+1-1 : ℕ) = n by omega, Nat.cast_add, Nat.cast_one]

/-- `∂_t B` in explicit form -/
private lemma deriv_zB_eq (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hR : Rz s t ≠ 0) :
    deriv (fun t : ℝ => zB n s t) t
      = ((((n-1:ℝ)*(Pz s t)^(n-2)*(-2*t*(1-s^2))*zb s t (n:ℝ)
            + (Pz s t)^(n-1)*zdb s t (n:ℝ)) * (Rz s t)^(n+1)
          - (Pz s t)^(n-1)*zb s t (n:ℝ) * ((n+1:ℝ)*(Rz s t)^n*(-s)))
          / ((Rz s t)^(n+1))^2) := by
  have hU : DifferentiableAt ℝ (fun t : ℝ => (Pz s t)^(n-1) * zb s t (n:ℝ)) t := by
    unfold Pz zb; fun_prop
  have hD : DifferentiableAt ℝ (fun t : ℝ => (Rz s t)^(n+1)) t := by unfold Rz; fun_prop
  unfold zB
  change deriv ((fun t : ℝ => (Pz s t)^(n-1) * zb s t (n:ℝ))
      / (fun t : ℝ => (Rz s t)^(n+1))) t = _
  rw [deriv_div hU hD (pow_ne_zero _ hR)]
  rw [deriv_U_t n hn, deriv_fun_pow (by unfold Rz; fun_prop), deriv_Rz_t]
  rw [show (n+1-1 : ℕ) = n by omega, Nat.cast_add, Nat.cast_one]

/-- `R^{n+2}·∂_s A = zDAs` -/
private lemma key_s (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hR : Rz s t ≠ 0) :
    (Rz s t)^(n+2) * deriv (fun s : ℝ => zA n s t) s = zDAs n s t := by
  rw [deriv_zA_eq n hn s t hR]
  unfold zDAs
  rw [← mul_div_assoc, div_eq_iff (by positivity)]
  ring_nf

/-- `R^{n+2}·∂_t B = zDBs` -/
private lemma key_t (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hR : Rz s t ≠ 0) :
    (Rz s t)^(n+2) * deriv (fun t : ℝ => zB n s t) t = zDBs n s t := by
  rw [deriv_zB_eq n hn s t hR]
  unfold zDBs
  rw [← mul_div_assoc, div_eq_iff (by positivity)]
  ring_nf

private lemma zDAs_eq (n : ℕ) (hn : 2 ≤ n) (s t : ℝ) :
    zDAs n s t
      = (Pz s t)^(n-2) * ((((n-1:ℝ)*(-2*s*(1-t^2))*za s t (n:ℝ)
            + (Pz s t)*zda s t (n:ℝ))*(Rz s t))
          - (n+1:ℝ)*(Pz s t)*za s t (n:ℝ)*(-t)) := by
  unfold zDAs
  rw [show n-1 = (n-2)+1 by omega, pow_succ]
  ring

private lemma zDBs_eq (n : ℕ) (hn : 2 ≤ n) (s t : ℝ) :
    zDBs n s t
      = (Pz s t)^(n-2) * ((((n-1:ℝ)*(-2*t*(1-s^2))*zb s t (n:ℝ)
            + (Pz s t)*zdb s t (n:ℝ))*(Rz s t))
          - (n+1:ℝ)*(Pz s t)*zb s t (n:ℝ)*(-s)) := by
  unfold zDBs
  rw [show n-1 = (n-2)+1 by omega, pow_succ]
  ring

/-- `zDAs + zDBs = P^{n-1}·S` -/
private lemma key_add (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    zDAs n s t + zDBs n s t = (Pz s t)^(n-1) * zS s t (n:ℝ) := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    unfold zDAs zDBs zS Pz Rz za zb zda zdb
    norm_num
    ring
  · have hn2 : 2 ≤ n := h
    rw [zDAs_eq n hn2 s t, zDBs_eq n hn2 s t]
    rw [show n-1 = (n-2)+1 by omega, pow_succ]
    linear_combination (Pz s t)^(n-2) * zcert_poly s t (n:ℝ)

/-- The combination `Φ_n = (n+1)²K_{n+1} + (7n²+7n+2)K_n - 8n²K_{n-1}` -/
def zPhi (n : ℕ) (s t : ℝ) : ℝ :=
  (((n+1:ℕ):ℝ))^2 * (Pz s t)^(n+1)/(Rz s t)^(n+2)
    + (7*(n:ℝ)^2+7*(n:ℝ)+2)*(Pz s t)^n/(Rz s t)^(n+1)
    - 8*(n:ℝ)^2*(Pz s t)^(n-1)/(Rz s t)^n

/-- **The divergence identity**: off the singular set `R = 0`,
`∂_s A + ∂_t B = Φ_n`. -/
private lemma deriv_identity (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hR : Rz s t ≠ 0) :
    deriv (fun s : ℝ => zA n s t) s + deriv (fun t : ℝ => zB n s t) t = zPhi n s t := by
  have hsum : (Rz s t)^(n+2) * (deriv (fun s : ℝ => zA n s t) s
      + deriv (fun t : ℝ => zB n s t) t) = (Pz s t)^(n-1) * zS s t (n:ℝ) := by
    rw [mul_add, key_s n hn s t hR, key_t n hn s t hR, key_add n hn s t]
  have hD : deriv (fun s : ℝ => zA n s t) s + deriv (fun t : ℝ => zB n s t) t
      = (Pz s t)^(n-1) * zS s t (n:ℝ) / (Rz s t)^(n+2) := by
    rw [eq_div_iff (pow_ne_zero _ hR), mul_comm]
    exact hsum
  rw [hD]
  unfold zS zPhi
  rw [show (n:ℝ)+1 = ((n+1:ℕ):ℝ) by push_cast; ring]
  have hP1 : (Pz s t)^(n+1) = (Pz s t)^(n-1)*(Pz s t)^2 := by
    rw [show n+1 = (n-1)+2 by omega, pow_add]
  have hP2 : (Pz s t)^n = (Pz s t)^(n-1)*(Pz s t) := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  have hR1 : (Rz s t)^(n+1) = (Rz s t)^(n+2)/(Rz s t) := by
    rw [eq_div_iff hR, ← pow_succ, show (n+1)+1 = n+2 by omega]
  have hR2 : (Rz s t)^n = (Rz s t)^(n+2)/(Rz s t)^2 := by
    rw [eq_div_iff (pow_ne_zero 2 hR), ← pow_add]
  rw [hP1, hP2, hR1, hR2]
  field_simp

/-- `K_m = P^m/R^{m+1}` -/
def zK (m : ℕ) (s t : ℝ) : ℝ := (Pz s t)^m / (Rz s t)^(m+1)

/-! ## Boundary vanishing of the certificate -/

private lemma za_zero_s (t n : ℝ) : za 0 t n = 0 := by simp [za]
private lemma za_one_s (t n : ℝ) : za 1 t n = 0 := by simp [za]
private lemma zb_zero_t (s n : ℝ) : zb s 0 n = 0 := by simp [zb]
private lemma zb_one_t (s n : ℝ) : zb s 1 n = 0 := by simp [zb]

private lemma zA_zero (n : ℕ) (t : ℝ) : zA n 0 t = 0 := by
  unfold zA Pz Rz
  rw [za_zero_s]
  simp

private lemma zA_one (n : ℕ) (t : ℝ) : zA n 1 t = 0 := by
  unfold zA Pz Rz
  rw [za_one_s]
  simp

private lemma zB_zero (n : ℕ) (s : ℝ) : zB n s 0 = 0 := by
  unfold zB Pz Rz
  rw [zb_zero_t]
  simp

private lemma zB_one (n : ℕ) (s : ℝ) : zB n s 1 = 0 := by
  unfold zB Pz Rz
  rw [zb_one_t]
  simp

/-! ## Elementary bounds on the unit square -/

private lemma Pz_nonneg {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ Pz s t := by
  unfold Pz
  exact mul_nonneg (by nlinarith) (by nlinarith)

/-- `P(s,t) ≤ R(s,t)²`, i.e. `(1-s²)(1-t²) ≤ (1-st)²`. -/
private lemma Pz_le_Rz_sq (s t : ℝ) : Pz s t ≤ (Rz s t)^2 := by
  unfold Pz Rz
  nlinarith [sq_nonneg (s-t)]

private lemma Rz_nonneg {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ Rz s t := by
  unfold Rz
  have : s*t ≤ 1 := le_trans (mul_le_of_le_one_right hs0 ht1) hs1
  linarith

/-- `R(s,t) ≥ (2-s-t)/2` on the unit square. -/
private lemma Rz_ge (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (2 - s - t)/2 ≤ Rz s t := by
  unfold Rz
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht0),
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs0)]

/-- `R(s,t) ≤ 2 - s - t` on the unit square. -/
private lemma Rz_le (s t : ℝ) (hs1 : s ≤ 1) (ht1 : t ≤ 1) : Rz s t ≤ 2 - s - t := by
  unfold Rz
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht1)]

private lemma two_sub_nonneg {s t : ℝ} (hs1 : s ≤ 1) (ht1 : t ≤ 1) : 0 ≤ 2 - s - t := by linarith

/-- `1 - t² ≤ 2(2-s-t)` on the unit square. -/
private lemma one_sub_sq_le (s t : ℝ) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - t^2 ≤ 2*(2-s-t) := by nlinarith

/-- `P(s,t) ≤ 4(1-s)(1-t)`. -/
private lemma Pz_le_four (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Pz s t ≤ 4*(1-s)*(1-t) := by
  have hP : Pz s t = (1-s)*(1-t)*((1+s)*(1+t)) := by unfold Pz; ring
  rw [hP]
  have hlt : (1+s)*(1+t) ≤ 4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1+s) (by linarith : (0:ℝ) ≤ 1+t)]
  have hnn : 0 ≤ (1-s)*(1-t) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlt hnn]

/-- `uv ≤ (u+v)²/4`. -/
private lemma mul_le_sq_div_four (u v : ℝ) : u*v ≤ (u+v)^2/4 := by nlinarith [sq_nonneg (u-v)]

/-! ## The certificate bounds -/

private def stf (s t n : ℝ) : ℝ :=
  n*(s^2*t^2+s^2+6*s*t-t^4+2*t^2-9) + (-2*t^4+4*t^2-2)

private def stfb (s t n : ℝ) : ℝ :=
  n*(s^4+2*s^3*t-s^2*t^2-6*s^2-4*s*t-t^2+9) + (2*s^4+2*s^3*t-6*s^2-2*s*t+4)

private lemma za_eq_stf (s t n : ℝ) : za s t n = -(1/2)*s*(1-s^2)*stf s t n := rfl
private lemma zb_eq_stfb (s t n : ℝ) : zb s t n = (1/2)*t*(1-t^2)*stfb s t n := rfl

private lemma stf_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |stf s t n| ≤ (12*n+8)*(2-s-t) := by
  have hfac : stf s t n
      = (s-1)*(n*(s*t^2+s+t^2+6*t+1))
        + (t-1)*(-(n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2)) := by
    unfold stf; ring
  have hbA : |n*(s*t^2+s+t^2+6*t+1)| ≤ 12*n+8 := by
    rw [abs_of_nonneg (mul_nonneg hn (by nlinarith [mul_nonneg hs0 (sq_nonneg t)]))]
    have e : s*t^2+s+t^2+6*t+1 ≤ 10 := by nlinarith [mul_nonneg hs0 (sq_nonneg t)]
    nlinarith [mul_le_mul_of_nonneg_left e hn, hn]
  have hbB : |-(n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2)| ≤ 12*n+8 := by
    rw [abs_neg, show n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2
        = n*(t^3+t^2-2*t-8) + (2*t^3+2*t^2-2*t-2) by ring]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hn]
    have hP : |t^3+t^2-2*t-8| ≤ 10 := by
      rw [abs_le]; constructor <;> nlinarith [ht0, ht1, sq_nonneg t]
    have hQ : |2*t^3+2*t^2-2*t-2| ≤ 8 := by
      rw [abs_le]; constructor <;> nlinarith [ht0, ht1, sq_nonneg t]
    nlinarith
  have h1 : |(s-1)*(n*(s*t^2+s+t^2+6*t+1))| ≤ (1-s)*(12*n+8) := by
    rw [abs_mul, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    nlinarith [hbA, hs1]
  have h2 : |(t-1)*(-(n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2))| ≤ (1-t)*(12*n+8) := by
    rw [abs_mul, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    nlinarith [hbB, ht1]
  calc |stf s t n|
      = |(s-1)*(n*(s*t^2+s+t^2+6*t+1))
          + (t-1)*(-(n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2))| := by rw [hfac]
    _ ≤ |(s-1)*(n*(s*t^2+s+t^2+6*t+1))|
          + |(t-1)*(-(n*t^3+n*t^2-2*n*t-8*n+2*t^3+2*t^2-2*t-2))| := abs_add_le _ _
    _ ≤ (1-s)*(12*n+8) + (1-t)*(12*n+8) := add_le_add h1 h2
    _ ≤ (12*n+8)*(2-s-t) := by nlinarith [hs1, ht1, hn]

private lemma stfb_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |stfb s t n| ≤ (16*n+12)*(2-s-t) := by
  have hfac : stfb s t n
      = (t-1)*(2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s)
        + (s-1)*(n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4) := by
    unfold stfb; ring
  have hbA : |2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s| ≤ 16*n+12 := by
    rw [show 2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s
        = n*(2*s^3-s^2*t-s^2-4*s-t-1) + (2*s^3-2*s) by ring]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hn]
    have hP : |2*s^3-s^2*t-s^2-4*s-t-1| ≤ 10 := by
      rw [abs_le]; constructor <;> nlinarith [hs0, hs1, ht0, ht1, sq_nonneg s]
    have hQ : |2*s^3-2*s| ≤ 4 := by
      rw [abs_le]; constructor <;> nlinarith [hs0, hs1, sq_nonneg s]
    nlinarith
  have hbB : |n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4| ≤ 16*n+12 := by
    rw [show n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4
        = n*(s^3+3*s^2-4*s-8) + (2*s^3+4*s^2-2*s-4) by ring]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hn]
    have hP : |s^3+3*s^2-4*s-8| ≤ 16 := by
      rw [abs_le]; constructor <;> nlinarith [hs0, hs1, sq_nonneg s]
    have hQ : |2*s^3+4*s^2-2*s-4| ≤ 12 := by
      rw [abs_le]; constructor <;> nlinarith [hs0, hs1, sq_nonneg s]
    nlinarith
  have h1 : |(t-1)*(2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s)| ≤ (1-t)*(16*n+12) := by
    rw [abs_mul, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    nlinarith [hbA, ht1]
  have h2 : |(s-1)*(n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4)| ≤ (1-s)*(16*n+12) := by
    rw [abs_mul, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    nlinarith [hbB, hs1]
  calc |stfb s t n|
      = |(t-1)*(2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s)
          + (s-1)*(n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4)| := by rw [hfac]
    _ ≤ |(t-1)*(2*n*s^3-n*s^2*t-n*s^2-4*n*s-n*t-n+2*s^3-2*s)|
          + |(s-1)*(n*s^3+3*n*s^2-4*n*s-8*n+2*s^3+4*s^2-2*s-4)| := abs_add_le _ _
    _ ≤ (1-t)*(16*n+12) + (1-s)*(16*n+12) := add_le_add h1 h2
    _ ≤ (16*n+12)*(2-s-t) := by nlinarith [hs1, ht1, hn]

/-! ## Bounds for `za, zda, zb, zdb` and for the divergence numerators -/

private lemma zda_eq_form (s t n : ℝ) :
    zda s t n = -(1/2)*((1-3*s^2)*stf s t n + s*(1-s^2)*(n*(2*s*t^2+2*s+6*t))) := by
  unfold zda stf; ring

private lemma zdb_eq_form (s t n : ℝ) :
    zdb s t n = (1/2)*((1-3*t^2)*stfb s t n
        + t*(1-t^2)*(n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s)) := by
  unfold zdb stfb; ring

private lemma za_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |za s t n| ≤ (12*n+8)*(2-s-t)^2 := by
  have h1 : |za s t n| = (1/2)*(s*(1-s^2))*|stf s t n| := by
    rw [za_eq_stf, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_nonneg hs0,
      abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1-s^2)]
    ring
  rw [h1]
  have h2 := stf_bound s t n hn hs0 hs1 ht0 ht1
  have h4 : 0 ≤ 2-s-t := two_sub_nonneg hs1 ht1
  have h5 : s*(1-s^2) ≤ 2*(2-s-t) := by
    nlinarith [mul_nonneg (sq_nonneg (s-1)) (by linarith : (0:ℝ) ≤ s+2), ht1, hs0, hs1]
  have hm : s*(1-s^2)*|stf s t n| ≤ (2*(2-s-t))*((12*n+8)*(2-s-t)) :=
    mul_le_mul h5 h2 (abs_nonneg _) (by linarith)
  nlinarith [hm, h4, hn]

private lemma zb_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |zb s t n| ≤ (16*n+12)*(2-s-t)^2 := by
  have h1 : |zb s t n| = (1/2)*(t*(1-t^2))*|stfb s t n| := by
    rw [zb_eq_stfb, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_nonneg ht0,
      abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1-t^2)]
    ring
  rw [h1]
  have h2 := stfb_bound s t n hn hs0 hs1 ht0 ht1
  have h4 : 0 ≤ 2-s-t := two_sub_nonneg hs1 ht1
  have h5 : t*(1-t^2) ≤ 2*(2-s-t) := by
    nlinarith [mul_nonneg (sq_nonneg (t-1)) (by linarith : (0:ℝ) ≤ t+2), hs1, ht0, ht1]
  have hm : t*(1-t^2)*|stfb s t n| ≤ (2*(2-s-t))*((16*n+12)*(2-s-t)) :=
    mul_le_mul h5 h2 (abs_nonneg _) (by linarith)
  nlinarith [hm, h4, hn]

private lemma zda_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |zda s t n| ≤ (28*n+12)*(2-s-t) := by
  rw [zda_eq_form]
  have h1 : |1-3*s^2| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, hs0, hs1]
  have h2 : |s*(1-s^2)| ≤ 2*(2-s-t) := by
    rw [abs_of_nonneg (mul_nonneg hs0 (by nlinarith))]
    nlinarith [mul_nonneg (sq_nonneg (s-1)) (by linarith : (0:ℝ) ≤ s+2), ht1, hs0, hs1]
  have h3 : |n*(2*s*t^2+2*s+6*t)| ≤ 10*n := by
    rw [abs_mul, abs_of_nonneg hn]
    have : |2*s*t^2+2*s+6*t| ≤ 10 := by
      rw [abs_of_nonneg (by nlinarith [mul_nonneg hs0 (sq_nonneg t)])]
      nlinarith [mul_nonneg hs0 (sq_nonneg t)]
    nlinarith [this, hn]
  have h4 := stf_bound s t n hn hs0 hs1 ht0 ht1
  have hst : |(1-3*s^2)*stf s t n| ≤ 3*((12*n+8)*(2-s-t)) := by
    rw [abs_mul]; exact mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
  have hss : |s*(1-s^2)*(n*(2*s*t^2+2*s+6*t))| ≤ (2*(2-s-t))*(10*n) := by
    rw [abs_mul]
    exact mul_le_mul h2 h3 (abs_nonneg _) (by nlinarith [two_sub_nonneg hs1 ht1])
  have e : |-(1/2)*((1-3*s^2)*stf s t n + s*(1-s^2)*(n*(2*s*t^2+2*s+6*t)))|
      = (1/2)*|(1-3*s^2)*stf s t n + s*(1-s^2)*(n*(2*s*t^2+2*s+6*t))| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [e]
  have h5 : 0 ≤ 2-s-t := two_sub_nonneg hs1 ht1
  refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _)
    (by norm_num : (0:ℝ) ≤ 1/2)) ?_
  nlinarith [hst, hss, h5, hn]

private lemma zdb_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |zdb s t n| ≤ (34*n+22)*(2-s-t) := by
  rw [zdb_eq_form]
  have h1 : |1-3*t^2| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg t, ht0, ht1]
  have h2 : |t*(1-t^2)| ≤ 2*(2-s-t) := by
    rw [abs_of_nonneg (mul_nonneg ht0 (by nlinarith))]
    nlinarith [mul_nonneg (sq_nonneg (t-1)) (by linarith : (0:ℝ) ≤ t+2), hs1, ht0, ht1]
  have h3 : |n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s| ≤ 10*n+4 := by
    rw [show n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s
        = n*(2*s^3-2*s^2*t-4*s-2*t) + (2*s^3-2*s) by ring]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hn]
    have hP : |2*s^3-2*s^2*t-4*s-2*t| ≤ 10 := by
      rw [abs_le]; constructor <;> nlinarith [hs0, hs1, ht0, ht1, sq_nonneg s]
    have hQ : |2*s^3-2*s| ≤ 4 := by rw [abs_le]; constructor <;> nlinarith [hs0, hs1, sq_nonneg s]
    nlinarith
  have h4 := stfb_bound s t n hn hs0 hs1 ht0 ht1
  have hst : |(1-3*t^2)*stfb s t n| ≤ 3*((16*n+12)*(2-s-t)) := by
    rw [abs_mul]; exact mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
  have hss : |t*(1-t^2)*(n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s)| ≤ (2*(2-s-t))*(10*n+4) := by
    rw [abs_mul]
    exact mul_le_mul h2 h3 (abs_nonneg _) (by nlinarith [two_sub_nonneg hs1 ht1])
  have e : |(1/2)*((1-3*t^2)*stfb s t n + t*(1-t^2)*(n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s))|
      = (1/2)*|(1-3*t^2)*stfb s t n + t*(1-t^2)*(n*(2*s^3-2*s^2*t-4*s-2*t)+2*s^3-2*s)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [e]
  have h5 : 0 ≤ 2-s-t := two_sub_nonneg hs1 ht1
  refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _)
    (by norm_num : (0:ℝ) ≤ 1/2)) ?_
  nlinarith [hst, hss, h5, hn]

private def zFs (s t n : ℝ) : ℝ :=
  (((n-1)*(-2*s*(1-t^2))*za s t n + (Pz s t)*zda s t n)*(Rz s t)
    - (n+1)*(Pz s t)*za s t n*(-t))

private def zGs (s t n : ℝ) : ℝ :=
  (((n-1)*(-2*t*(1-s^2))*zb s t n + (Pz s t)*zdb s t n)*(Rz s t)
    - (n+1)*(Pz s t)*zb s t n*(-s))

private lemma Pz_abs_bound (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |Pz s t| ≤ (2-s-t)^2 := by
  rw [abs_of_nonneg (Pz_nonneg hs0 hs1 ht0 ht1)]
  refine le_trans (Pz_le_Rz_sq s t) ?_
  nlinarith [Rz_nonneg hs0 hs1 ht0 ht1, Rz_le s t hs1 ht1, two_sub_nonneg hs1 ht1]

private lemma Rz_abs_bound (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |Rz s t| ≤ 2-s-t := by
  rw [abs_of_nonneg (Rz_nonneg hs0 hs1 ht0 ht1)]
  exact Rz_le s t hs1 ht1

private lemma one_sub_sq_abs (s t : ℝ) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |1-t^2| ≤ 2*(2-s-t) := by
  rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1-t^2)]
  exact one_sub_sq_le s t hs1 ht0 ht1

private lemma factor_abs_bound1 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |(-2)*s*(1-t^2)| ≤ 4*(2-s-t) := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hs0]
  have h := one_sub_sq_abs s t hs1 ht0 ht1
  nlinarith [h, abs_nonneg (1-t^2), two_sub_nonneg hs1 ht1, hs1]

private lemma factor_abs_bound2 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |(-2)*t*(1-s^2)| ≤ 4*(2-s-t) := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg ht0]
  have h := one_sub_sq_abs t s ht1 hs0 hs1
  have h' : |1-s^2| ≤ 2*(2-s-t) := by
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1-s^2)]; nlinarith [hs1, ht1]
  nlinarith [h', abs_nonneg (1-s^2), two_sub_nonneg hs1 ht1, ht1]

private lemma zFs_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |zFs s t n| ≤ (5*(n+1)*(12*n+8) + (28*n+12))*(2-s-t)^4 := by
  have hza := za_bound s t n hn hs0 hs1 ht0 ht1
  have hzda := zda_bound s t n hn hs0 hs1 ht0 ht1
  have hPz := Pz_abs_bound s t hs0 hs1 ht0 ht1
  have hRz := Rz_abs_bound s t hs0 hs1 ht0 ht1
  have hfac := factor_abs_bound1 s t hs0 hs1 ht0 ht1
  have h4 : (0:ℝ) ≤ 2-s-t := two_sub_nonneg hs1 ht1
  have hinner1 : |((-2)*s*(1-t^2))*za s t n| ≤ (4*(2-s-t)) * ((12*n+8)*(2-s-t)^2) := by
    rw [abs_mul]
    exact mul_le_mul hfac hza (abs_nonneg _) (by positivity)
  have e1 : |(n-1)*(-2*s*(1-t^2))*za s t n|
      ≤ (abs (n-1)) * ((4*(2-s-t)) * ((12*n+8)*(2-s-t)^2)) := by
    rw [show (n-1)*(-2*s*(1-t^2))*za s t n = (n-1)*(((-2)*s*(1-t^2))*za s t n) by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_left hinner1 (abs_nonneg _)
  have e2 : |(Pz s t)*zda s t n| ≤ (2-s-t)^2 * ((28*n+12)*(2-s-t)) := by
    rw [abs_mul]
    exact mul_le_mul hPz hzda (abs_nonneg _) (by positivity)
  have hzat : |za s t n*(-t)| ≤ (12*n+8)*(2-s-t)^2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg ht0]
    calc |za s t n| * t ≤ ((12*n+8)*(2-s-t)^2) * t := mul_le_mul_of_nonneg_right hza ht0
      _ ≤ ((12*n+8)*(2-s-t)^2) * 1 := by
          apply mul_le_mul_of_nonneg_left ht1
          positivity
      _ = (12*n+8)*(2-s-t)^2 := by ring
  have e3 : |(n+1)*(Pz s t)*za s t n*(-t)| ≤ (n+1) * ((2-s-t)^2*((12*n+8)*(2-s-t)^2)) := by
    rw [show (n+1)*(Pz s t)*za s t n*(-t) = (n+1)*((Pz s t)*((za s t n)*(-t))) by ring,
      abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ n+1)]
    have hmul : (n+1) * |(Pz s t)*((za s t n)*(-t))|
        ≤ (n+1) * ((2-s-t)^2*((12*n+8)*(2-s-t)^2)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [abs_mul]
        exact mul_le_mul hPz hzat (abs_nonneg _) (by positivity)
      · linarith
    exact hmul
  have hP1 : |(n-1)*(-2*s*(1-t^2))*za s t n| * |Rz s t|
      ≤ (abs (n-1)) * ((4*(2-s-t)) * ((12*n+8)*(2-s-t)^2)) * (2-s-t) :=
    mul_le_mul e1 hRz (abs_nonneg _) (by positivity)
  have hP2 : |(Pz s t)*zda s t n| * |Rz s t| ≤ (2-s-t)^2 * ((28*n+12)*(2-s-t)) * (2-s-t) :=
    mul_le_mul e2 hRz (abs_nonneg _) (by positivity)
  have key : |zFs s t n| ≤ |(n-1)*(-2*s*(1-t^2))*za s t n| * |Rz s t|
      + |(Pz s t)*zda s t n| * |Rz s t| + |(n+1)*(Pz s t)*za s t n*(-t)| := by
    have he : zFs s t n
        = (((n-1)*(-2*s*(1-t^2))*za s t n)*(Rz s t) + ((Pz s t)*zda s t n)*(Rz s t))
          + (-((n+1)*(Pz s t)*za s t n*(-t))) := by unfold zFs; ring
    rw [he]
    have h1 : |((n-1)*(-2*s*(1-t^2))*za s t n)*(Rz s t)|
        = |(n-1)*(-2*s*(1-t^2))*za s t n| * |Rz s t| := abs_mul _ _
    have h2 : |((Pz s t)*zda s t n)*(Rz s t)| = |(Pz s t)*zda s t n| * |Rz s t| := abs_mul _ _
    calc |((n-1)*(-2*s*(1-t^2))*za s t n)*(Rz s t) + ((Pz s t)*zda s t n)*(Rz s t)
            + -((n+1)*(Pz s t)*za s t n*(-t))|
        ≤ |((n-1)*(-2*s*(1-t^2))*za s t n)*(Rz s t) + ((Pz s t)*zda s t n)*(Rz s t)|
            + |(n+1)*(Pz s t)*za s t n*(-t)| := by
          refine le_trans (abs_add_le _ _) ?_; rw [abs_neg]
      _ ≤ (|((n-1)*(-2*s*(1-t^2))*za s t n)*(Rz s t)|
            + |((Pz s t)*zda s t n)*(Rz s t)|) + |(n+1)*(Pz s t)*za s t n*(-t)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
      _ = |(n-1)*(-2*s*(1-t^2))*za s t n| * |Rz s t|
            + |(Pz s t)*zda s t n| * |Rz s t| + |(n+1)*(Pz s t)*za s t n*(-t)| := by
          rw [h1, h2]
  have hnn : (abs (n-1)) ≤ n+1 := by
    rcases le_total 1 n with h | h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ n-1)]; linarith
    · rw [abs_of_nonpos (by linarith : n-1 ≤ 0)]; linarith
  have h1 : (abs (n-1))*(4*(2-s-t)*((12*n+8)*(2-s-t)^2))*(2-s-t)
      ≤ (n+1)*(4*(2-s-t)*((12*n+8)*(2-s-t)^2))*(2-s-t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnn (by positivity)) (by positivity)
  nlinarith [key, hP1, hP2, e3, h1, h4, hn]

private lemma zGs_bound (s t n : ℝ) (hn : 0 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |zGs s t n| ≤ (5*(n+1)*(16*n+12) + (34*n+22))*(2-s-t)^4 := by
  have hzb := zb_bound s t n hn hs0 hs1 ht0 ht1
  have hzdb := zdb_bound s t n hn hs0 hs1 ht0 ht1
  have hPz := Pz_abs_bound s t hs0 hs1 ht0 ht1
  have hRz := Rz_abs_bound s t hs0 hs1 ht0 ht1
  have hfac := factor_abs_bound2 s t hs0 hs1 ht0 ht1
  have h4 : (0:ℝ) ≤ 2-s-t := two_sub_nonneg hs1 ht1
  have hinner1 : |((-2)*t*(1-s^2))*zb s t n| ≤ (4*(2-s-t)) * ((16*n+12)*(2-s-t)^2) := by
    rw [abs_mul]
    exact mul_le_mul hfac hzb (abs_nonneg _) (by positivity)
  have e1 : |(n-1)*(-2*t*(1-s^2))*zb s t n|
      ≤ (abs (n-1)) * ((4*(2-s-t)) * ((16*n+12)*(2-s-t)^2)) := by
    rw [show (n-1)*(-2*t*(1-s^2))*zb s t n = (n-1)*(((-2)*t*(1-s^2))*zb s t n) by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_left hinner1 (abs_nonneg _)
  have e2 : |(Pz s t)*zdb s t n| ≤ (2-s-t)^2 * ((34*n+22)*(2-s-t)) := by
    rw [abs_mul]
    exact mul_le_mul hPz hzdb (abs_nonneg _) (by positivity)
  have hzbs : |zb s t n*(-s)| ≤ (16*n+12)*(2-s-t)^2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hs0]
    calc |zb s t n| * s ≤ ((16*n+12)*(2-s-t)^2) * s := mul_le_mul_of_nonneg_right hzb hs0
      _ ≤ ((16*n+12)*(2-s-t)^2) * 1 := by
          apply mul_le_mul_of_nonneg_left hs1
          positivity
      _ = (16*n+12)*(2-s-t)^2 := by ring
  have e3 : |(n+1)*(Pz s t)*zb s t n*(-s)| ≤ (n+1) * ((2-s-t)^2*((16*n+12)*(2-s-t)^2)) := by
    rw [show (n+1)*(Pz s t)*zb s t n*(-s) = (n+1)*((Pz s t)*((zb s t n)*(-s))) by ring,
      abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ n+1)]
    have hmul : (n+1) * |(Pz s t)*((zb s t n)*(-s))|
        ≤ (n+1) * ((2-s-t)^2*((16*n+12)*(2-s-t)^2)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [abs_mul]
        exact mul_le_mul hPz hzbs (abs_nonneg _) (by positivity)
      · linarith
    exact hmul
  have hP1 : |(n-1)*(-2*t*(1-s^2))*zb s t n| * |Rz s t|
      ≤ (abs (n-1)) * ((4*(2-s-t)) * ((16*n+12)*(2-s-t)^2)) * (2-s-t) :=
    mul_le_mul e1 hRz (abs_nonneg _) (by positivity)
  have hP2 : |(Pz s t)*zdb s t n| * |Rz s t| ≤ (2-s-t)^2 * ((34*n+22)*(2-s-t)) * (2-s-t) :=
    mul_le_mul e2 hRz (abs_nonneg _) (by positivity)
  have key : |zGs s t n| ≤ |(n-1)*(-2*t*(1-s^2))*zb s t n| * |Rz s t|
      + |(Pz s t)*zdb s t n| * |Rz s t| + |(n+1)*(Pz s t)*zb s t n*(-s)| := by
    have he : zGs s t n
        = (((n-1)*(-2*t*(1-s^2))*zb s t n)*(Rz s t) + ((Pz s t)*zdb s t n)*(Rz s t))
          + (-((n+1)*(Pz s t)*zb s t n*(-s))) := by unfold zGs; ring
    rw [he]
    have h1 : |((n-1)*(-2*t*(1-s^2))*zb s t n)*(Rz s t)|
        = |(n-1)*(-2*t*(1-s^2))*zb s t n| * |Rz s t| := abs_mul _ _
    have h2 : |((Pz s t)*zdb s t n)*(Rz s t)| = |(Pz s t)*zdb s t n| * |Rz s t| := abs_mul _ _
    calc |((n-1)*(-2*t*(1-s^2))*zb s t n)*(Rz s t) + ((Pz s t)*zdb s t n)*(Rz s t)
            + -((n+1)*(Pz s t)*zb s t n*(-s))|
        ≤ |((n-1)*(-2*t*(1-s^2))*zb s t n)*(Rz s t) + ((Pz s t)*zdb s t n)*(Rz s t)|
            + |(n+1)*(Pz s t)*zb s t n*(-s)| := by
          refine le_trans (abs_add_le _ _) ?_; rw [abs_neg]
      _ ≤ (|((n-1)*(-2*t*(1-s^2))*zb s t n)*(Rz s t)|
            + |((Pz s t)*zdb s t n)*(Rz s t)|) + |(n+1)*(Pz s t)*zb s t n*(-s)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
      _ = |(n-1)*(-2*t*(1-s^2))*zb s t n| * |Rz s t|
            + |(Pz s t)*zdb s t n| * |Rz s t| + |(n+1)*(Pz s t)*zb s t n*(-s)| := by
          rw [h1, h2]
  have hnn : (abs (n-1)) ≤ n+1 := by
    rcases le_total 1 n with h | h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ n-1)]; linarith
    · rw [abs_of_nonpos (by linarith : n-1 ≤ 0)]; linarith
  have h1 : (abs (n-1))*(4*(2-s-t)*((16*n+12)*(2-s-t)^2))*(2-s-t)
      ≤ (n+1)*(4*(2-s-t)*((16*n+12)*(2-s-t)^2))*(2-s-t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnn (by positivity)) (by positivity)
  nlinarith [key, hP1, hP2, e3, h1, h4, hn]

/-- The constant in the integrability bound on `∂_s A`. -/
def zDK (n : ℕ) : ℝ :=
  (5*((n:ℝ)+1)*(12*(n:ℝ)+8) + (28*(n:ℝ)+12)) * (4:ℝ)^n + 320

private lemma zDAs_bound (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |zDAs n s t| ≤ zDK n * (Rz s t)^(n+1) := by
  have h4 : (0:ℝ) ≤ 2-s-t := two_sub_nonneg hs1 ht1
  have hRz0 : 0 ≤ Rz s t := Rz_nonneg hs0 hs1 ht0 ht1
  have hge := Rz_ge s t hs0 hs1 ht0 ht1
  have h2 : (2-s-t) ≤ 2 := by linarith
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    have hzz : zDAs 1 s t = zda s t 1 * Rz s t + 2 * t * za s t 1 := by
      unfold zDAs; norm_num; ring
    have hzda := zda_bound s t 1 (by norm_num) hs0 hs1 ht0 ht1
    have hza := za_bound s t 1 (by norm_num) hs0 hs1 ht0 ht1
    have hRzb := Rz_abs_bound s t hs0 hs1 ht0 ht1
    have hza' : |za s t 1| ≤ 20*(2-s-t)^2 := by
      have h := hza
      rw [show (12:ℝ)*1+8 = 20 by norm_num] at h
      exact h
    have h1 : |zDAs 1 s t| ≤ 80*(2-s-t)^2 := by
      rw [hzz]
      have hA : |zda s t 1 * Rz s t| ≤ 40*(2-s-t)*(2-s-t) := by
        rw [abs_mul]
        have := hzda; rw [show (28:ℝ)*1+12 = 40 by norm_num] at this
        exact mul_le_mul this hRzb (abs_nonneg _) (by positivity)
      have hB : |2 * t * za s t 1| ≤ 40*(2-s-t)^2 := by
        rw [show (2:ℝ)*t*za s t 1 = 2*(t*za s t 1) by ring, abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have ht_abs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
        calc 2 * |t * za s t 1| ≤ 2 * (1 * (20*(2-s-t)^2)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
              rw [abs_mul]
              exact mul_le_mul ht_abs hza' (abs_nonneg _) (by positivity)
          _ = 40*(2-s-t)^2 := by ring
      refine le_trans (abs_add_le _ _) ?_
      nlinarith [hA, hB, h4]
    have h5 : (2-s-t)^2 ≤ 4*(Rz s t)^2 := by nlinarith [hge, h4, hRz0]
    have hd : 320 ≤ zDK 1 := by
      unfold zDK; norm_num
    calc |zDAs 1 s t| ≤ 80*(2-s-t)^2 := h1
      _ ≤ 320*(Rz s t)^2 := by nlinarith [h5]
      _ ≤ zDK 1 * (Rz s t)^2 := by
          apply mul_le_mul_of_nonneg_right hd (by positivity)
      _ = zDK 1 * (Rz s t)^(1+1) := by norm_num
  · have hn2 : 2 ≤ n := h
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hPz := Pz_abs_bound s t hs0 hs1 ht0 ht1
    have hF := zFs_bound s t (n:ℝ) hnR hs0 hs1 ht0 ht1
    have hPzb : Pz s t ≤ (2-s-t)^2 := by
      have := hPz; rwa [abs_of_nonneg (Pz_nonneg hs0 hs1 ht0 ht1)] at this
    have hPzs : |(Pz s t)^(n-2)| ≤ (2-s-t)^(2*(n-2)) := by
      rw [abs_of_nonneg (pow_nonneg (Pz_nonneg hs0 hs1 ht0 ht1) _)]
      calc (Pz s t)^(n-2) ≤ ((2-s-t)^2)^(n-2) :=
            pow_le_pow_left₀ (Pz_nonneg hs0 hs1 ht0 ht1) hPzb (n-2)
        _ = (2-s-t)^(2*(n-2)) := by rw [← pow_mul]
    have step : |(Pz s t)^(n-2) * zFs s t (n:ℝ)|
        ≤ (2-s-t)^(2*(n-2)) * ((5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12))*(2-s-t)^4) := by
      rw [abs_mul]
      exact mul_le_mul hPzs hF (abs_nonneg _) (by positivity)
    have hp : (2-s-t)^(2*(n-2)) * (2-s-t)^4 = (2-s-t)^(2*n) := by
      rw [← pow_add, show 2*(n-2)+4 = 2*n by omega]
    have hq : (2-s-t)^(2*n) ≤ (4:ℝ)^n * (Rz s t)^(n+1) := by
      have h1 : (2-s-t)^(2*n) = (2-s-t)^(n-1) * (2-s-t)^(n+1) := by
        rw [← pow_add, show n-1+(n+1) = 2*n by omega]
      rw [h1]
      have hA : (2-s-t)^(n-1) ≤ 2^(n-1) :=
        pow_le_pow_left₀ h4 h2 (n-1)
      have hB : (2-s-t)^(n+1) ≤ (2:ℝ)^(n+1) * (Rz s t)^(n+1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ h4 (by linarith : 2-s-t ≤ 2*Rz s t) (n+1)
      calc (2-s-t)^(n-1) * (2-s-t)^(n+1)
          ≤ 2^(n-1) * ((2:ℝ)^(n+1) * (Rz s t)^(n+1)) :=
            mul_le_mul hA hB (by positivity) (by positivity)
        _ = (4:ℝ)^n * (Rz s t)^(n+1) := by
            rw [← mul_assoc, ← pow_add, show n-1+(n+1) = 2*n by omega, pow_mul]
            norm_num
    have hdk : (5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12)) * (4:ℝ)^n ≤ zDK n := by
      unfold zDK; linarith
    have hzDAs_eq : zDAs n s t = (Pz s t)^(n-2) * zFs s t (n:ℝ) := by
      rw [zDAs_eq n hn2 s t]; rfl
    rw [hzDAs_eq]
    calc |(Pz s t)^(n-2) * zFs s t (n:ℝ)|
        ≤ (2-s-t)^(2*(n-2)) * ((5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12))*(2-s-t)^4) := step
      _ = (5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12)) * (2-s-t)^(2*n) := by rw [← hp]; ring
      _ ≤ (5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12)) * ((4:ℝ)^n * (Rz s t)^(n+1)) := by
          apply mul_le_mul_of_nonneg_left hq; positivity
      _ = ((5*((n:ℝ)+1)*(12*(n:ℝ)+8)+(28*(n:ℝ)+12)) * (4:ℝ)^n) * (Rz s t)^(n+1) := by ring
      _ ≤ zDK n * (Rz s t)^(n+1) := by
          apply mul_le_mul_of_nonneg_right hdk (by positivity)

/-! ## Integrability of `∂_s A` -/

private lemma intInt_rpow_one_sub :
    IntervalIntegrable (fun x : ℝ => (1-x) ^ (-(1/2) : ℝ)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := (1:ℝ)) (r := -(1/2))
    (by norm_num)).comp_sub_left 1
  simpa using h.symm

private lemma integrableOn_rpow_one_sub :
    IntegrableOn (fun x : ℝ => (1-x) ^ (-(1/2) : ℝ)) (Set.uIoc (0:ℝ) 1) := by
  rw [← intervalIntegrable_iff]
  exact intInt_rpow_one_sub

private lemma integrableOn_dom :
    IntegrableOn (fun p : ℝ × ℝ => (1-p.1)^(-(1/2):ℝ) * (1-p.2)^(-(1/2):ℝ))
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  rw [IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict]
  exact Integrable.mul_prod integrableOn_rpow_one_sub integrableOn_rpow_one_sub

private lemma inv_two_sub_le (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (2-s-t)⁻¹ ≤ (1-s)^(-(1/2) : ℝ) * (1-t)^(-(1/2) : ℝ) := by
  have hs : 0 < 1-s := by linarith
  have ht : 0 < 1-t := by linarith
  have h2 : 0 < 2-s-t := by linarith
  have hR : (1-s)^(-(1/2) : ℝ) * (1-t)^(-(1/2) : ℝ) = (Real.sqrt ((1-s)*(1-t)))⁻¹ := by
    rw [Real.rpow_neg hs.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← mul_inv, ← Real.sqrt_mul hs.le]
  rw [hR, inv_le_inv₀ h2 (Real.sqrt_pos.mpr (mul_pos hs ht)), Real.sqrt_le_left (by linarith)]
  nlinarith

private lemma ae_ne_one : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 1 ∧ p.2 ≠ 1 := by
  have h1 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    show (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | ¬(p.1 ≠ 1)} = 0
    rw [show {p : ℝ × ℝ | ¬(p.1 ≠ 1)} = {1} ×ˢ (Set.univ : Set ℝ) by ext p; simp]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]
    simp
  have h2 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.2 ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    show (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | ¬(p.2 ≠ 1)} = 0
    rw [show {p : ℝ × ℝ | ¬(p.2 ≠ 1)} = (Set.univ : Set ℝ) ×ˢ {1} by ext p; simp]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]
    simp
  exact h1.and h2

private lemma ae_deriv_zA_le (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ p ∂(volume.restrict (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1)),
      ‖deriv (fun s : ℝ => zA n s p.2) p.1‖
        ≤ (2*zDK n) * ((1-p.1)^(-(1/2):ℝ) * (1-p.2)^(-(1/2):ℝ)) := by
  rw [ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)]
  filter_upwards [ae_ne_one] with p hpne hpS
  rcases hpS with ⟨hp1, hp2⟩
  have hp1' : p.1 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp1
  have hp2' : p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp2
  rcases hp1' with ⟨hp1a, hp1b⟩
  rcases hp2' with ⟨hp2a, hp2b⟩
  have hp1lt : p.1 < 1 := lt_of_le_of_ne hp1b hpne.1
  have hp2lt : p.2 < 1 := lt_of_le_of_ne hp2b hpne.2
  have hR : Rz p.1 p.2 ≠ 0 := by
    intro hc
    have hpr : p.1 * p.2 = 1 := by unfold Rz at hc; linarith
    have h1 : p.1 = 1 := by nlinarith [hp1a, hp1b, hp2a, hp2b, hpr]
    exact hpne.1 h1
  have hkey := key_s n hn p.1 p.2 hR
  have hb := zDAs_bound n hn p.1 p.2 (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b
  have hRpos : 0 < Rz p.1 p.2 := lt_of_le_of_ne (Rz_nonneg (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b) (Ne.symm hR)
  have hge := Rz_ge p.1 p.2 (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b
  have h2' : 0 < 2-p.1-p.2 := by linarith
  rw [Real.norm_eq_abs,
    show deriv (fun s : ℝ => zA n s p.2) p.1 = zDAs n p.1 p.2 / (Rz p.1 p.2)^(n+2) by
      rw [eq_div_iff (pow_ne_zero _ hR), mul_comm]; exact hkey,
    abs_div, abs_of_pos (pow_pos hRpos _)]
  have hstep : |zDAs n p.1 p.2| / (Rz p.1 p.2)^(n+2)
      ≤ 2*zDK n * ((1-p.1)^(-(1/2):ℝ) * (1-p.2)^(-(1/2):ℝ)) := by
    have h1 : |zDAs n p.1 p.2| / (Rz p.1 p.2)^(n+2)
        ≤ zDK n * (Rz p.1 p.2)^(n+1) / (Rz p.1 p.2)^(n+2) :=
      div_le_div_of_nonneg_right hb (by positivity)
    have hpw : (Rz p.1 p.2)^(n+1) / (Rz p.1 p.2)^(n+2) = (Rz p.1 p.2)⁻¹ := by
      rw [div_eq_iff (pow_ne_zero _ (ne_of_gt hRpos)), eq_comm,
        inv_mul_eq_iff_eq_mul₀ (ne_of_gt hRpos), ← pow_succ']
    have h2 : zDK n * (Rz p.1 p.2)^(n+1) / (Rz p.1 p.2)^(n+2) = zDK n * (Rz p.1 p.2)⁻¹ := by
      rw [mul_div_assoc, hpw]
    have hz0 : 0 ≤ zDK n := by unfold zDK; positivity
    have h3 : zDK n * (Rz p.1 p.2)⁻¹ ≤ 2*zDK n * (2-p.1-p.2)⁻¹ := by
      have hb1 : (2-p.1-p.2) ≤ 2*Rz p.1 p.2 := by linarith
      have hb2 : (2*Rz p.1 p.2)⁻¹ ≤ (2-p.1-p.2)⁻¹ := inv_anti₀ h2' hb1
      have hb3 : (Rz p.1 p.2)⁻¹ = 2*(2*Rz p.1 p.2)⁻¹ := by rw [mul_inv]; ring
      rw [hb3]
      nlinarith [hb2, hz0]
    have h4 := inv_two_sub_le p.1 p.2 (le_of_lt hp1a) hp1lt (le_of_lt hp2a) hp2lt
    exact le_trans (le_trans h1 (le_of_eq h2)) (le_trans h3 (by nlinarith))
  exact hstep

private lemma zRz_ne_of_ne_one {p : ℝ × ℝ} (hp1 : p.1 ∈ Set.Ioc (0:ℝ) 1)
    (hp2 : p.2 ∈ Set.Ioc (0:ℝ) 1) (hne : p.1 ≠ 1) : Rz p.1 p.2 ≠ 0 := by
  rcases hp1 with ⟨hp1a, hp1b⟩
  rcases hp2 with ⟨hp2a, hp2b⟩
  intro hc
  have hpr : p.1 * p.2 = 1 := by unfold Rz at hc; linarith
  exact hne (by nlinarith [hp1a, hp1b, hp2a, hp2b, hpr])

private lemma ae_rational_eq_deriv (n : ℕ) (hn : 1 ≤ n) :
    (fun p : ℝ × ℝ => zDAs n p.1 p.2 / (Rz p.1 p.2)^(n+2))
      =ᵐ[volume.restrict (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1)]
      (fun p : ℝ × ℝ => deriv (fun s : ℝ => zA n s p.2) p.1) := by
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)]
  filter_upwards [ae_ne_one] with p hpne hpS
  rcases hpS with ⟨hp1, hp2⟩
  have hp1' : p.1 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp1
  have hp2' : p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp2
  have hR := zRz_ne_of_ne_one hp1' hp2' hpne.1
  rw [show deriv (fun s : ℝ => zA n s p.2) p.1 = zDAs n p.1 p.2 / (Rz p.1 p.2)^(n+2) by
    rw [eq_div_iff (pow_ne_zero _ hR), mul_comm]; exact key_s n hn p.1 p.2 hR]

private lemma integrableOn_deriv_zA (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun p : ℝ × ℝ => deriv (fun s : ℝ => zA n s p.2) p.1)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  have hgm : IntegrableOn
      (fun p : ℝ × ℝ => (2*zDK n) * ((1-p.1)^(-(1/2):ℝ) * (1-p.2)^(-(1/2):ℝ)))
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := integrableOn_dom.const_mul _
  refine Integrable.mono' hgm ?_ (ae_deriv_zA_le n hn)
  have hnum : Measurable (fun p : ℝ × ℝ => zDAs n p.1 p.2) := by
    have hc : Continuous (fun p : ℝ × ℝ => zDAs n p.1 p.2) := by
      unfold zDAs Pz Rz za zda; fun_prop
    exact hc.measurable
  have hden : Measurable (fun p : ℝ × ℝ => ((Rz p.1 p.2)^(n+2))⁻¹) := by
    refine Measurable.inv ?_
    have hc : Continuous (fun p : ℝ × ℝ => (Rz p.1 p.2)^(n+2)) := by unfold Rz; fun_prop
    exact hc.measurable
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => zDAs n p.1 p.2 / (Rz p.1 p.2)^(n+2))
      (volume.restrict (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1)) := by
    have h : (fun p : ℝ × ℝ => zDAs n p.1 p.2 / (Rz p.1 p.2)^(n+2))
        = fun p => zDAs n p.1 p.2 * ((Rz p.1 p.2)^(n+2))⁻¹ := by funext p; ring
    rw [h]
    exact (hnum.mul hden).aestronglyMeasurable
  exact hmeas.congr (ae_rational_eq_deriv n hn)

private lemma contDiffOn_zA (n : ℕ) (t : ℝ) (ht : t < 1) :
    ContDiffOn ℝ 1 (fun s : ℝ => zA n s t) (Set.Icc 0 1) := by
  have hRz : ∀ s ∈ Set.Icc (0:ℝ) 1, Rz s t ≠ 0 := by
    intro s hs
    have h : Rz s t = 1 - s*t := rfl
    have hst : s*t < 1 := by
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr (le_of_lt ht)), hlt]
      · rw [heq, one_mul]; exact ht
    linarith
  unfold zA
  refine ContDiffOn.div (by unfold Pz za; fun_prop) (by unfold Rz; fun_prop) ?_
  intro x hx
  exact pow_ne_zero _ (hRz x hx)

private lemma contDiffOn_zB (n : ℕ) (s : ℝ) (hs : s < 1) :
    ContDiffOn ℝ 1 (fun t : ℝ => zB n s t) (Set.Icc 0 1) := by
  have hRz : ∀ t ∈ Set.Icc (0:ℝ) 1, Rz s t ≠ 0 := by
    intro t ht
    have h : Rz s t = 1 - s*t := rfl
    have hst : s*t < 1 := by
      rcases le_total 0 s with h0 | h0
      · nlinarith [mul_nonneg h0 (sub_nonneg.mpr ht.2), hs]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg h0 ht.1]
    linarith
  unfold zB
  refine ContDiffOn.div (by unfold Pz zb; fun_prop) (by unfold Rz; fun_prop) ?_
  intro x hx
  exact pow_ne_zero _ (hRz x hx)

private lemma ae_ne_one_real : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
  rw [MeasureTheory.ae_iff]
  show (volume : Measure ℝ) {x : ℝ | ¬(x ≠ 1)} = 0
  rw [show {x : ℝ | ¬(x ≠ 1)} = {1} by ext x; simp]
  simp

private lemma zPhi_integral_zero (n : ℕ) (hn : 1 ≤ n) :
    ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zPhi n s t = 0 := by
  have hInner : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (0:ℝ) 1 →
      ∫ t in (0:ℝ)..1, zPhi n s t
        = ∫ t in (0:ℝ)..1, deriv (fun s' : ℝ => zA n s' t) s := by
    filter_upwards [ae_ne_one_real] with s hsne hsIoc
    have hsIoc' : s ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hsIoc
    rcases hsIoc' with ⟨hs0, hs1⟩
    have hs1' : s < 1 := lt_of_le_of_ne hs1 hsne
    have hRzC : ∀ t ∈ Set.Icc (0:ℝ) 1, Rz s t ≠ 0 := by
      intro t ht
      have h : Rz s t = 1 - s*t := rfl
      have hst : s*t < 1 := by
        have h1 : s*t ≤ s := by nlinarith [mul_nonneg (le_of_lt hs0) (sub_nonneg.mpr ht.2)]
        linarith [h1, hs1']
      rw [h]
      intro hc
      linarith
    have hpt : ∀ t ∈ Set.uIcc (0:ℝ) 1, zPhi n s t
        = deriv (fun s' : ℝ => zA n s' t) s + deriv (fun t' : ℝ => zB n s t') t := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact (deriv_identity n hn s t (hRzC t ht)).symm
    have hIA : IntervalIntegrable (fun t : ℝ => deriv (fun s' : ℝ => zA n s' t) s) volume 0 1 := by
      have hcont : ContinuousOn (fun t : ℝ => zDAs n s t / (Rz s t)^(n+2)) (Set.uIcc (0:ℝ) 1) := by
        refine ContinuousOn.div (by unfold zDAs Pz Rz za zda; fun_prop)
          (by unfold Rz; fun_prop) ?_
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact pow_ne_zero _ (hRzC t ht)
      refine (hcont.intervalIntegrable).congr_uIoo ?_
      intro t ht
      rw [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have hR := hRzC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      change zDAs n s t / (Rz s t)^(n+2) = deriv (fun s' : ℝ => zA n s' t) s
      rw [div_eq_iff (pow_ne_zero _ hR), mul_comm]
      exact (key_s n hn s t hR).symm
    have hIB : IntervalIntegrable (fun t : ℝ => deriv (fun t' : ℝ => zB n s t') t) volume 0 1 := by
      have hcont : ContinuousOn (fun t : ℝ => zDBs n s t / (Rz s t)^(n+2)) (Set.uIcc (0:ℝ) 1) := by
        refine ContinuousOn.div (by unfold zDBs Pz Rz zb zdb; fun_prop)
          (by unfold Rz; fun_prop) ?_
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact pow_ne_zero _ (hRzC t ht)
      refine (hcont.intervalIntegrable).congr_uIoo ?_
      intro t ht
      rw [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have hR := hRzC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      change zDBs n s t / (Rz s t)^(n+2) = deriv (fun t' : ℝ => zB n s t') t
      rw [div_eq_iff (pow_ne_zero _ hR), mul_comm]
      exact (key_t n hn s t hR).symm
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hIA hIB,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc (contDiffOn_zB n s hs1') zero_le_one,
      zB_one, zB_zero, sub_zero, add_zero]
  have hmain : ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zPhi n s t
      = ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, deriv (fun s' : ℝ => zA n s' t) s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hInner] with s hs
    exact hs
  rw [hmain, intervalIntegral_intervalIntegral_swap
    (F := fun s t : ℝ => deriv (fun s' : ℝ => zA n s' t) s) (integrableOn_deriv_zA n hn)]
  have hInner2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ∫ s in (0:ℝ)..1, deriv (fun s' : ℝ => zA n s' t) s = 0 := by
    filter_upwards [ae_ne_one_real] with t htne htIoc
    have htIoc' : t ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using htIoc
    rcases htIoc' with ⟨ht0, ht1⟩
    have ht1' : t < 1 := lt_of_le_of_ne ht1 htne
    rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc (contDiffOn_zA n t ht1') zero_le_one,
      zA_one, zA_zero, sub_zero]
  have hz : (∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, deriv (fun s' : ℝ => zA n s' t) s) = 0 := by
    have h1 : (∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, deriv (fun s' : ℝ => zA n s' t) s)
        = ∫ t in (0:ℝ)..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hInner2] with t ht
      exact ht
    rw [h1]; simp
  rw [hz]

private lemma aestronglyMeasurable_zK (m : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => zK m p.1 p.2)
      (volume.restrict (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1)) := by
  have hnum : Measurable (fun p : ℝ × ℝ => (Pz p.1 p.2)^m) :=
    (by unfold Pz; fun_prop : Continuous (fun p : ℝ × ℝ => (Pz p.1 p.2)^m)).measurable
  have hden : Measurable (fun p : ℝ × ℝ => ((Rz p.1 p.2)^(m+1))⁻¹) := by
    refine Measurable.inv ?_
    exact (by unfold Rz; fun_prop : Continuous (fun p : ℝ × ℝ => (Rz p.1 p.2)^(m+1))).measurable
  have h : (fun p : ℝ × ℝ => zK m p.1 p.2)
      = fun p => (Pz p.1 p.2)^m * ((Rz p.1 p.2)^(m+1))⁻¹ := by
    funext p; unfold zK; ring
  rw [h]
  exact (hnum.mul hden).aestronglyMeasurable

private lemma volume_prod_S :
    (volume : Measure (ℝ × ℝ)) (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) < ∞ := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]
  simp [Real.volume_uIoc]

private lemma integrableOn_zK_pos (m : ℕ) (hm : 1 ≤ m) :
    IntegrableOn (fun p : ℝ × ℝ => zK m p.1 p.2)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  rw [IntegrableOn]
  refine IntegrableOn.of_bound volume_prod_S (aestronglyMeasurable_zK m) 1 ?_
  rw [ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)]
  filter_upwards with p hp
  rcases hp with ⟨hp1, hp2⟩
  have hp1' : p.1 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp1
  have hp2' : p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp2
  rcases hp1' with ⟨hp1a, hp1b⟩
  rcases hp2' with ⟨hp2a, hp2b⟩
  have hRnn : 0 ≤ Rz p.1 p.2 := Rz_nonneg (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b
  have hPnn : 0 ≤ Pz p.1 p.2 := Pz_nonneg (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b
  have hR1 : Rz p.1 p.2 ≤ 1 := by
    have h : Rz p.1 p.2 = 1 - p.1*p.2 := rfl
    rw [h]; nlinarith [mul_nonneg (le_of_lt hp1a) (le_of_lt hp2a)]
  rw [Real.norm_eq_abs]
  unfold zK
  rw [abs_of_nonneg (div_nonneg (pow_nonneg hPnn m) (pow_nonneg hRnn (m+1)))]
  rcases eq_or_ne (Rz p.1 p.2) 0 with hRz0 | hRz0
  · rw [hRz0]; simp
  · calc (Pz p.1 p.2)^m / (Rz p.1 p.2)^(m+1)
        ≤ ((Rz p.1 p.2)^2)^m / (Rz p.1 p.2)^(m+1) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hPnn (Pz_le_Rz_sq p.1 p.2) m) (by positivity)
      _ = (Rz p.1 p.2)^(m-1) := by
            rw [← pow_mul, div_eq_iff (pow_ne_zero _ hRz0), ← pow_add]
            congr 1; omega
      _ ≤ 1 := pow_le_one₀ hRnn hR1

private lemma inv_Rz_le (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (Rz s t)⁻¹ ≤ (1-s)^(-(1/2) : ℝ) * (1-t)^(-(1/2) : ℝ) := by
  have hs : 0 < 1-s := by linarith
  have ht : 0 < 1-t := by linarith
  have hs1' : s ≤ 1 := le_of_lt hs1
  have ht1' : t ≤ 1 := le_of_lt ht1
  have hR : (1-s)*(1-t) ≤ (Rz s t)^2 := by
    have h1 : Rz s t = 1 - s*t := rfl
    rw [h1]
    have ha : (1:ℝ) - s ≤ 1 - s*t := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr ht1')]
    have hb : (1:ℝ) - t ≤ 1 - s*t := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs1')]
    have hc : 0 ≤ (1:ℝ) - t := by linarith
    have hd : 0 ≤ (1:ℝ) - s*t := by nlinarith [mul_nonneg hs0 ht0, hs1, ht1]
    nlinarith [mul_le_mul ha hb hc hd]
  have hRpos : 0 < Rz s t := by
    have h1 : Rz s t = 1 - s*t := rfl
    rw [h1]; nlinarith [mul_nonneg hs0 ht0, hs1, ht1]
  have hsqrt : Real.sqrt ((1-s)*(1-t)) ≤ Rz s t := by
    rw [Real.sqrt_le_left (le_of_lt hRpos)]
    exact hR
  have hsqrt_exp : (1-s)^(-(1/2) : ℝ) * (1-t)^(-(1/2) : ℝ)
      = (Real.sqrt ((1-s)*(1-t)))⁻¹ := by
    rw [Real.rpow_neg hs.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← mul_inv, ← Real.sqrt_mul hs.le]
  rw [hsqrt_exp]
  exact inv_anti₀ (Real.sqrt_pos.mpr (mul_pos hs ht)) hsqrt

private lemma integrableOn_zK_zero :
    IntegrableOn (fun p : ℝ × ℝ => zK 0 p.1 p.2)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  rw [IntegrableOn]
  refine Integrable.mono' integrableOn_dom (aestronglyMeasurable_zK 0) ?_
  rw [ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)]
  filter_upwards [ae_ne_one] with p hpne hp
  rcases hp with ⟨hp1, hp2⟩
  have hp1' : p.1 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp1
  have hp2' : p.2 ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hp2
  have hR := zRz_ne_of_ne_one hp1' hp2' hpne.1
  rcases hp1' with ⟨hp1a, hp1b⟩
  rcases hp2' with ⟨hp2a, hp2b⟩
  have hp1lt : p.1 < 1 := lt_of_le_of_ne hp1b hpne.1
  have hp2lt : p.2 < 1 := lt_of_le_of_ne hp2b hpne.2
  have hRpos : 0 < Rz p.1 p.2 :=
    lt_of_le_of_ne (Rz_nonneg (le_of_lt hp1a) hp1b (le_of_lt hp2a) hp2b) (Ne.symm hR)
  have hdom := inv_Rz_le p.1 p.2 (le_of_lt hp1a) hp1lt (le_of_lt hp2a) hp2lt
  rw [Real.norm_eq_abs]
  unfold zK
  rw [show Pz p.1 p.2 ^ 0 / Rz p.1 p.2 ^ (0+1) = (Rz p.1 p.2)⁻¹ by simp]
  rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hRpos))]
  exact hdom

private lemma integrableOn_zK (m : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => zK m p.1 p.2)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; exact integrableOn_zK_zero
  · exact integrableOn_zK_pos m h

private lemma zK_eq_statement (m : ℕ) (s t : ℝ) :
    zK m s t = (1-s^2)^m * (1-t^2)^m / (1-s*t)^(m+1) := by
  unfold zK Pz Rz
  rw [mul_pow]

private lemma zPhi_pt (n : ℕ) (hn : 1 ≤ n) (s t : ℝ) :
    zPhi n s t = (((n+1:ℕ):ℝ))^2 * ((1-s^2)^(n+1)*(1-t^2)^(n+1)/(1-s*t)^(n+2))
      + (7*(n:ℝ)^2+7*(n:ℝ)+2) * ((1-s^2)^n*(1-t^2)^n/(1-s*t)^(n+1))
      - 8*(n:ℝ)^2 * ((1-s^2)^(n-1)*(1-t^2)^(n-1)/(1-s*t)^n) := by
  unfold zPhi Pz Rz
  simp only [mul_pow]
  ring

private lemma fubini_iterated (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (Function.uncurry f)
      (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1)) :
    ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t
      = ∫ p in (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1), f p.1 p.2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  conv_lhs => enter [2, x]; rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [← Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact (setIntegral_prod (f := Function.uncurry f) hf).symm

private def zG (m : ℕ) (s t : ℝ) : ℝ := (1-s^2)^m * (1-t^2)^m / (1-s*t)^(m+1)

private lemma zG_eq_zK (m : ℕ) (s t : ℝ) : zG m s t = zK m s t := by
  rw [zK_eq_statement]; rfl

/-- **The ζ-side Zagier (Franel) recurrence** for
`I_n = ∫₀¹∫₀¹ (1-s²)ⁿ(1-t²)ⁿ/(1-st)^{n+1} ds dt`. -/
theorem zetaintegral_recurrence_parametric :
    ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ) : ℝ)) ^ 2 *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
           (1 - s^2)^(n+1) * (1 - t^2)^(n+1) / (1 - s*t)^(n+2))
      = - (7 * (((n : ℕ) : ℝ))^2 + 7 * (((n : ℕ) : ℝ)) + 2) *
          (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
             (1 - s^2)^n * (1 - t^2)^n / (1 - s*t)^(n+1))
        + 8 * (((n : ℕ) : ℝ))^2 *
          (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
             (1 - s^2)^(n-1) * (1 - t^2)^(n-1) / (1 - s*t)^n) := by
  intro n hn
  set S : Set (ℝ × ℝ) := Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1 with hS
  have hPhi_eq : (fun p : ℝ × ℝ => zPhi n p.1 p.2)
      = (fun p : ℝ × ℝ => (((n+1:ℕ):ℝ))^2 * zG (n+1) p.1 p.2)
        + (fun p : ℝ × ℝ => (7*(n:ℝ)^2+7*(n:ℝ)+2)*zG n p.1 p.2)
        - (fun p : ℝ × ℝ => (8*(n:ℝ)^2)*zG (n-1) p.1 p.2) := by
    funext p; simp only [Pi.add_apply, Pi.sub_apply]
    simpa [zG, Nat.sub_add_cancel hn] using zPhi_pt n hn p.1 p.2
  have hGint : ∀ m, IntegrableOn (fun p : ℝ × ℝ => zG m p.1 p.2) S := by
    intro m
    have h : (fun p : ℝ × ℝ => zG m p.1 p.2) = fun p => zK m p.1 p.2 := by
      funext p; exact zG_eq_zK m p.1 p.2
    rw [h]; exact integrableOn_zK m
  have hPhi_int : IntegrableOn (fun p : ℝ × ℝ => zPhi n p.1 p.2) S := by
    rw [hPhi_eq]
    exact (((hGint (n+1)).const_mul _).add ((hGint n).const_mul _)).sub
      ((hGint (n-1)).const_mul _)
  have h2 : (∫ p in S, zPhi n p.1 p.2)
      = (((n+1:ℕ):ℝ))^2 * (∫ p in S, zG (n+1) p.1 p.2)
        + (7*(n:ℝ)^2+7*(n:ℝ)+2) * (∫ p in S, zG n p.1 p.2)
        - 8*(n:ℝ)^2 * (∫ p in S, zG (n-1) p.1 p.2) := by
    have hA : IntegrableOn (fun p : ℝ × ℝ => (((n+1:ℕ):ℝ)^2 * zG (n+1) p.1 p.2)) S :=
      (hGint (n+1)).const_mul _
    have hB : IntegrableOn (fun p : ℝ × ℝ => (7*(n:ℝ)^2+7*(n:ℝ)+2) * zG n p.1 p.2) S :=
      (hGint n).const_mul _
    have hC : IntegrableOn (fun p : ℝ × ℝ => (8*(n:ℝ)^2) * zG (n-1) p.1 p.2) S :=
      (hGint (n-1)).const_mul _
    have hAB : IntegrableOn (fun p : ℝ × ℝ => (((n+1:ℕ):ℝ)^2 * zG (n+1) p.1 p.2)
        + (7*(n:ℝ)^2+7*(n:ℝ)+2) * zG n p.1 p.2) S := hA.add hB
    rw [hPhi_eq]
    rw [show ((fun p : ℝ × ℝ => (((n+1:ℕ):ℝ)^2 * zG (n+1) p.1 p.2))
        + (fun p : ℝ × ℝ => (7*(n:ℝ)^2+7*(n:ℝ)+2)*zG n p.1 p.2))
        - (fun p : ℝ × ℝ => (8*(n:ℝ)^2)*zG (n-1) p.1 p.2)
        = fun p : ℝ × ℝ => (((n+1:ℕ):ℝ)^2 * zG (n+1) p.1 p.2
          + (7*(n:ℝ)^2+7*(n:ℝ)+2)*zG n p.1 p.2) - (8*(n:ℝ)^2)*zG (n-1) p.1 p.2 from by
      funext p; simp]
    rw [MeasureTheory.integral_sub hAB hC]
    rw [MeasureTheory.integral_add hA hB]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have h3 : ∀ m, (∫ p in S, zG m p.1 p.2)
      = ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zG m s t := by
    intro m
    refine (fubini_iterated (fun s t => zG m s t) ?_).symm
    have h : Function.uncurry (fun s t : ℝ => zG m s t)
        = fun p : ℝ × ℝ => zG m p.1 p.2 := rfl
    rw [h]; exact hGint m
  have hsplit : (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zPhi n s t)
      = (((n+1:ℕ):ℝ))^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zG (n+1) s t)
        + (7*(n:ℝ)^2+7*(n:ℝ)+2) * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zG n s t)
        - 8*(n:ℝ)^2 * (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, zG (n-1) s t) := by
    rw [fubini_iterated (fun s t => zPhi n s t) (by
      have h : Function.uncurry (fun s t : ℝ => zPhi n s t)
          = fun p : ℝ × ℝ => zPhi n p.1 p.2 := rfl
      rw [h]; exact hPhi_int), h2, h3 (n+1), h3 n, h3 (n-1)]
  have h0 := zPhi_integral_zero n hn
  rw [hsplit] at h0
  simp only [zG, show (n:ℕ)+1+1 = n+2 by omega, Nat.sub_add_cancel hn] at h0 ⊢
  linarith [h0]

end
end Commons.Analysis.Integral