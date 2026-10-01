/-
# `tf72fK_t_moment_nonneg`

The signed kernel `tf72fK t = (1 - 2 exp (-(6/7) t)) * tf72f (6/7) t` has non-negative first
moment on the support `[0, 7/3]`.  The proof follows the route sketched in the statement:

* the fourth-order Taylor upper bound `exp (-x) ≤ 1 - x + x²/2 - x³/6 + x⁴/24` for `0 ≤ x`
  (proved here from the monotonicity of `φ y = exp y * (1 - y + y²/2 - y³/6 + y⁴/24)`, whose
  derivative is `exp y * y⁴/24 ≥ 0`) gives the pointwise lower bound
  `1 - 2 exp (-(6/7) t) ≥ -1 + (12/7) t - (36/49) t² + (72/343) t³ - (108/2401) t⁴`;
* since `t · tf72f (6/7) t ≥ 0`, integrating gives
  `∫₀^{7/3} t · tf72fK t ≥ -M 1 + (12/7) M 2 - (36/49) M 3 + (72/343) M 4 - (108/2401) M 5`
  with `M k = ∫₀^{7/3} t^k · tf72f (6/7) t` the moments of `tf72f_moment`;
* that combination of moments equals the positive rational `104/66825`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.tf72fK_defs
import Submission.Work.ZeroFreeTables.tf72f_moment

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables

/-! ## The fourth-order Taylor upper bound for the exponential -/

/-- The quartic Taylor polynomial `1 - y + y²/2 - y³/6 + y⁴/24` of `exp` at `0`, written in
product form so that `simp` computes its algebraic derivative without meeting `Nat.sub`
exponents. -/
def tf72fTaylor4 : Polynomial ℝ :=
  Polynomial.C 1 - Polynomial.X + Polynomial.C (1/2) * (Polynomial.X * Polynomial.X)
    - Polynomial.C (1/6) * (Polynomial.X * Polynomial.X * Polynomial.X)
    + Polynomial.C (1/24) * (Polynomial.X * Polynomial.X * Polynomial.X * Polynomial.X)

/-- `φ y = exp y * (1 - y + y²/2 - y³/6 + y⁴/24)` has derivative `exp y * y⁴/24`. -/
lemma tf72f_taylor4_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp y * (1 - y + y^2/2 - y^3/6 + y^4/24))
      (Real.exp x * (x^4/24)) x := by
  have hpoly : HasDerivAt (fun y : ℝ => tf72fTaylor4.eval y) (tf72fTaylor4.derivative.eval x) x :=
    tf72fTaylor4.hasDerivAt x
  have hfun : (fun y : ℝ => tf72fTaylor4.eval y)
      = fun y : ℝ => 1 - y + y^2/2 - y^3/6 + y^4/24 := by
    funext y
    simp only [tf72fTaylor4, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hder : tf72fTaylor4.derivative.eval x = -1 + x - x^2/2 + x^3/6 := by
    simp only [tf72fTaylor4, Polynomial.derivative_sub, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
    ring
  rw [hfun, hder] at hpoly
  have hmul : HasDerivAt (fun y : ℝ => Real.exp y * (1 - y + y^2/2 - y^3/6 + y^4/24))
      (Real.exp x * (1 - x + x^2/2 - x^3/6 + x^4/24)
        + Real.exp x * (-1 + x - x^2/2 + x^3/6)) x :=
    (Real.hasDerivAt_exp x).mul hpoly
  have hval : Real.exp x * (1 - x + x^2/2 - x^3/6 + x^4/24)
      + Real.exp x * (-1 + x - x^2/2 + x^3/6) = Real.exp x * (x^4/24) := by ring
  rw [hval] at hmul
  exact hmul

/-- Fourth-order Taylor upper bound for the exponential at a negative argument:
for `x ≥ 0`, `exp (-x) ≤ 1 - x + x^2/2 - x^3/6 + x^4/24`. -/
lemma tf72fK_taylor4_bound (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x^2/2 - x^3/6 + x^4/24 := by
  have hmono : Monotone (fun y : ℝ => Real.exp y * (1 - y + y^2/2 - y^3/6 + y^4/24)) :=
    monotone_of_hasDerivAt_nonneg tf72f_taylor4_hasDerivAt (fun y => by positivity)
  have h1 : (1:ℝ) ≤ Real.exp x * (1 - x + x^2/2 - x^3/6 + x^4/24) := by
    have h := hmono hx
    simpa using h
  have h2 : Real.exp (-x) * (Real.exp x * (1 - x + x^2/2 - x^3/6 + x^4/24))
      = 1 - x + x^2/2 - x^3/6 + x^4/24 := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-x)).le
  rwa [mul_one, h2] at h3

/-! ## The pointwise lower bound for the signed kernel -/

/-- For `t ≥ 0`, the Taylor bound turns `1 - 2 exp (-(6/7) t)` into the quintic lower bound
`-1 + (12/7) t - (36/49) t² + (72/343) t³ - (108/2401) t⁴`; multiplying by the non-negative
`t · tf72f (6/7) t` gives the pointwise bound on the integrand. -/
lemma tf72fK_t_moment_pointwise (t : ℝ) (ht : 0 ≤ t) :
    (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3 + (72/343) * t^4
      + (-(108/2401)) * t^5) * tf72f (6/7) t) ≤ t * tf72fK t := by
  have hx : (0:ℝ) ≤ (6/7) * t := by positivity
  have hT := tf72fK_taylor4_bound ((6/7) * t) hx
  have harg : -((6/7) * t) = -(6/7) * t := by ring
  have hT' : Real.exp (-(6/7) * t)
      ≤ 1 - (6/7)*t + ((6/7)*t)^2/2 - ((6/7)*t)^3/6 + ((6/7)*t)^4/24 := by
    rw [← harg]
    exact hT
  have hQ : (-1:ℝ) + (12/7)*t - (36/49)*t^2 + (72/343)*t^3 - (108/2401)*t^4
      ≤ 1 - 2 * Real.exp (-(6/7) * t) := by
    have hid : (1:ℝ) - 2 * (1 - (6/7)*t + ((6/7)*t)^2/2 - ((6/7)*t)^3/6 + ((6/7)*t)^4/24)
        = (-1) + (12/7)*t - (36/49)*t^2 + (72/343)*t^3 - (108/2401)*t^4 := by ring
    linarith [hT', hid]
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  have hfac : 0 ≤ t * tf72f (6/7) t := mul_nonneg ht hf
  calc (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3 + (72/343) * t^4
        + (-(108/2401)) * t^5) * tf72f (6/7) t)
      = ((-1:ℝ) + (12/7)*t - (36/49)*t^2 + (72/343)*t^3 - (108/2401)*t^4)
          * (t * tf72f (6/7) t) := by ring
    _ ≤ (1 - 2 * Real.exp (-(6/7) * t)) * (t * tf72f (6/7) t) :=
        mul_le_mul_of_nonneg_right hQ hfac
    _ = t * tf72fK t := by unfold tf72fK; ring

/-! ## The value of the lower-bound integral -/

/-- The polynomial lower bound of `tf72fK_t_moment_pointwise`, integrated against
`tf72f (6/7)` over `[0, 7/3]`, equals the positive rational `104/66825`: split into the five
moments `M k = ∫₀^{7/3} t^k · tf72f (6/7) t` (`k = 1,…,5`) evaluated by `tf72f_moment`. -/
lemma tf72fK_moment_lincomb :
    (∫ t in (0:ℝ)..(7/3),
      ((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3 + (72/343) * t^4
        + (-(108/2401)) * t^5) * tf72f (6/7) t) = 104/66825 := by
  have hab : (0:ℝ) ≤ 7/3 := by norm_num
  have hcontf : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) := by
    refine (tf72f_cont (6/7) (by norm_num)).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ht.1
  have hint : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => t^k * tf72f (6/7) t) volume (0:ℝ) (7/3) :=
    fun k => ((continuous_id.pow k).continuousOn.mul hcontf).intervalIntegrable
  have hA : IntervalIntegrable (fun t : ℝ => (-1:ℝ) * (t^1 * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (hint 1).const_mul (-1)
  have hB : IntervalIntegrable (fun t : ℝ => (12/7) * (t^2 * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (hint 2).const_mul (12/7)
  have hC : IntervalIntegrable (fun t : ℝ => (-(36/49)) * (t^3 * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (hint 3).const_mul (-(36/49))
  have hD : IntervalIntegrable (fun t : ℝ => (72/343) * (t^4 * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (hint 4).const_mul (72/343)
  have hE : IntervalIntegrable (fun t : ℝ => (-(108/2401)) * (t^5 * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    (hint 5).const_mul (-(108/2401))
  rw [show (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3 + (72/343) * t^4
        + (-(108/2401)) * t^5) * tf72f (6/7) t))
      = fun t : ℝ => (-1:ℝ) * (t^1 * tf72f (6/7) t)
          + ((12/7) * (t^2 * tf72f (6/7) t)
          + ((-(36/49)) * (t^3 * tf72f (6/7) t)
          + ((72/343) * (t^4 * tf72f (6/7) t)
          + (-(108/2401)) * (t^5 * tf72f (6/7) t)))) from by funext t; ring]
  rw [intervalIntegral.integral_add hA (hB.add (hC.add (hD.add hE))),
      intervalIntegral.integral_add hB (hC.add (hD.add hE)),
      intervalIntegral.integral_add hC (hD.add hE),
      intervalIntegral.integral_add hD hE,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [tf72f_moment 1, tf72f_moment 2, tf72f_moment 3, tf72f_moment 4, tf72f_moment 5]
  norm_num

/-! ## The main theorem -/

/-- The signed kernel `tf72fK t = (1 - 2 exp (-(6/7) t)) * tf72f (6/7) t` has non-negative
first moment.  Numerically `∫_0^{7/3} t * tf72fK t = 1592/45 - (784/3) exp (-2) ≈ 0.01016 > 0`.
A route: the Taylor bound `exp (-x) ≤ 1 - x + x^2/2 - x^3/6 + x^4/24` for `0 ≤ x`
(equivalently `24 exp (-x) ≤ x^4 - 4x^3 + 12x^2 - 24x + 24`, the difference with `24 exp (-x)`
increasing with derivative `x^4 exp x ≥ 0` at `x ≥ 0`) gives the pointwise bound
`1 - 2 exp (-(6/7) t) ≥ -1 + (12/7) t - (36/49) t^2 + (72/343) t^3 - (108/2401) t^4`,
and the resulting rational combination of moments
`-M 1 + (12/7) M 2 - (36/49) M 3 + (72/343) M 4 - (108/2401) M 5` (with
`M k = tf72fL_mom k = ∫_0^{7/3} t^k tf72f (6/7) t`, available from `tf72f_moment`) equals the
positive rational `104/66825`. -/
theorem tf72fK_t_moment_nonneg :
    0 ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := by
  have hab : (0:ℝ) ≤ 7/3 := by norm_num
  have hcontf : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) := by
    refine (tf72f_cont (6/7) (by norm_num)).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ht.1
  have hcontK : ContinuousOn (fun t : ℝ => t * tf72fK t) (Set.uIcc (0:ℝ) (7/3)) := by
    have hexp : Continuous (fun t : ℝ => (1:ℝ) - 2 * Real.exp (-(6/7) * t)) := by fun_prop
    have h : ContinuousOn (fun t : ℝ => (t * ((1:ℝ) - 2 * Real.exp (-(6/7) * t)))
        * tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
      (continuous_id.continuousOn.mul hexp.continuousOn).mul hcontf
    simpa only [tf72fK, mul_assoc] using h
  have hcontL : ContinuousOn (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t)) (Set.uIcc (0:ℝ) (7/3)) :=
    (by fun_prop : Continuous (fun t : ℝ => ((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5))).continuousOn.mul hcontf
  have hintK : IntervalIntegrable (fun t : ℝ => t * tf72fK t) volume (0:ℝ) (7/3) :=
    hcontK.intervalIntegrable
  have hintL : IntervalIntegrable (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2
      + (-(36/49)) * t^3 + (72/343) * t^4 + (-(108/2401)) * t^5)
      * tf72f (6/7) t)) volume (0:ℝ) (7/3) :=
    hcontL.intervalIntegrable
  have hle := intervalIntegral.integral_mono_on hab hintL hintK
    (fun t ht => tf72fK_t_moment_pointwise t (Set.mem_Icc.mp ht).1)
  have hval : (∫ t in (0:ℝ)..(7/3), (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t)) = 104/66825 :=
    tf72fK_moment_lincomb
  have hpos : (0:ℝ) < 104/66825 := by norm_num
  linarith

end Work.ZeroFreeTables
