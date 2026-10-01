/-
# ZeroFreeTables — tf72f_moment

The moments of HB Lemma 7.2's optimal test function `tf72f` with the limiting
slope `λ = 6/7` (so that the support `[0, 2/λ] = [0, 7/3]`):

  `∫_0^{7/3} t^k · f(t) dt
     = (32/35)·(7/3)^(k+1)/(k+1) − (288/343)·(7/3)^(k+3)/(k+3)
       + (864/2401)·(7/3)^(k+4)/(k+4) − (7776/588245)·(7/3)^(k+6)/(k+6)`.

On `[0, 7/3]` the test function is the polynomial
`f(t) = (λ/30)(2 − λt)³(4 + 6λt + λ²t²)`
and, writing `a = λt`, the quartic factor satisfies the polynomial identity

  `(2 − a)³(4 + 6a + a²) = 32 − 40a² + 20a³ − a⁵`.

Hence `t^k f(t) = (λ/30)(32 t^k − 40λ² t^(k+2) + 20λ³ t^(k+3) − λ⁵ t^(k+5))`
and the moment reduces to four elementary monomial integrals `∫_0^a t^n`,
which is `tf72f_moment_lin` below.  The remaining step is the arithmetic
identity `tf72f_moment_alg`, obtained by rewriting the powers `(7/3)^(k+j)`
relative to `(7/3)^(k+1)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

open scoped Interval
open MeasureTheory

namespace Work.ZeroFreeTables

/-- Moment integral of a quintic-corrected monomial: for every `a : ℝ`,

  `∫_0^a t^k (c0 + c1 t² + c2 t³ + c3 t⁵) dt
     = c0 a^(k+1)/(k+1) + c1 a^(k+3)/(k+3) + c2 a^(k+4)/(k+4) + c3 a^(k+6)/(k+6)`.

Each term is integrated with the elementary `∫_0^a t^n = a^(n+1)/(n+1)`. -/
lemma tf72f_moment_lin (k : ℕ) (a c0 c1 c2 c3 : ℝ) :
    (∫ t in (0:ℝ)..a, t^k * (c0 + c1 * t^2 + c2 * t^3 + c3 * t^5))
      = c0 * a^(k+1)/((k:ℝ)+1) + c1 * a^(k+3)/((k:ℝ)+3)
        + c2 * a^(k+4)/((k:ℝ)+4) + c3 * a^(k+6)/((k:ℝ)+6) := by
  -- expand the integrand into a linear combination of monomials
  have hfun : ∀ t : ℝ, t^k * (c0 + c1*t^2 + c2*t^3 + c3*t^5)
      = c0 * t^k + c1 * t^(k+2) + c2 * t^(k+3) + c3 * t^(k+5) := by
    intro t
    have e1 : t^k * t^2 = t^(k+2) := by rw [← pow_add]
    have e2 : t^k * t^3 = t^(k+3) := by rw [← pow_add]
    have e3 : t^k * t^5 = t^(k+5) := by rw [← pow_add]
    rw [show t^k * (c0 + c1 * t^2 + c2 * t^3 + c3 * t^5)
          = c0 * t^k + c1 * (t^k * t^2) + c2 * (t^k * t^3) + c3 * (t^k * t^5) by ring,
        e1, e2, e3]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t)]
  have h0 : IntervalIntegrable (fun t:ℝ => c0 * t^k) volume (0:ℝ) a :=
    (continuous_const.mul (continuous_id.pow k)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t:ℝ => c1 * t^(k+2)) volume (0:ℝ) a :=
    (continuous_const.mul (continuous_id.pow (k+2))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t:ℝ => c2 * t^(k+3)) volume (0:ℝ) a :=
    (continuous_const.mul (continuous_id.pow (k+3))).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t:ℝ => c3 * t^(k+5)) volume (0:ℝ) a :=
    (continuous_const.mul (continuous_id.pow (k+5))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h1 |>.add h2) h3,
      intervalIntegral.integral_add (h0.add h1) h2,
      intervalIntegral.integral_add h0 h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_pow, integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero k), zero_pow (Nat.succ_ne_zero (k+2)),
    zero_pow (Nat.succ_ne_zero (k+3)), zero_pow (Nat.succ_ne_zero (k+5)), sub_zero]
  push_cast
  ring

/-- The arithmetic core of `tf72f_moment`, with `λ = 6/7` and `2/λ = 7/3`:
the moment formula produced by `tf72f_moment_lin` collapses to the stated
closed form.  This is the identity `(6/7)·(7/3) = 2`: each power `(7/3)^(k+j)`
is rewritten as `(7/3)^(k+1) · (7/3)^(j-1)`. -/
lemma tf72f_moment_alg (k : ℕ) :
    ((6/7/30)*32) * (7/3:ℝ)^(k+1)/((k:ℝ)+1)
    + ((6/7/30)*(-(40*(6/7)^2))) * (7/3)^(k+3)/((k:ℝ)+3)
    + ((6/7/30)*(20*(6/7)^3)) * (7/3)^(k+4)/((k:ℝ)+4)
    + ((6/7/30)*(-((6/7)^5))) * (7/3)^(k+6)/((k:ℝ)+6)
  = (32/35)*(7/3)^(k+1)/((k:ℝ)+1) + (-288/343)*(7/3)^(k+3)/((k:ℝ)+3)
    + (864/2401)*(7/3)^(k+4)/((k:ℝ)+4) + (-7776/588245)*(7/3)^(k+6)/((k:ℝ)+6) := by
  have h1 : (7/3:ℝ)^(k+3) = (7/3)^(k+1) * (7/3)^2 := by
    rw [show k+3 = (k+1)+2 by omega, pow_add]
  have h2 : (7/3:ℝ)^(k+4) = (7/3)^(k+1) * (7/3)^3 := by
    rw [show k+4 = (k+1)+3 by omega, pow_add]
  have h3 : (7/3:ℝ)^(k+6) = (7/3)^(k+1) * (7/3)^5 := by
    rw [show k+6 = (k+1)+5 by omega, pow_add]
  rw [h1, h2, h3]
  have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
  have hk3 : ((k:ℝ)+3) ≠ 0 := by positivity
  have hk4 : ((k:ℝ)+4) ≠ 0 := by positivity
  have hk6 : ((k:ℝ)+6) ≠ 0 := by positivity
  field_simp
  ring

/-- **The moments of HB Lemma 7.2's test function at `λ = 6/7`.**  On the support
`[0, 7/3]` the integrand is the quintic `(6/7/30)·t^k·(2 − (6/7)t)³(4 + 6(6/7)t + (6/7)²t²)`,
whose expanded form is `t^k·(c0 + c1 t² + c2 t³ + c3 t⁵)` with the coefficients
`c0 = (6/7/30)·32`, `c1 = −(6/7/30)·40·(6/7)²`, `c2 = (6/7/30)·20·(6/7)³`,
`c3 = −(6/7/30)·(6/7)⁵`; integrating term by term (`tf72f_moment_lin`) and
simplifying (`tf72f_moment_alg`) gives the closed form. -/
theorem tf72f_moment (k : ℕ) :
    (∫ t in (0:ℝ)..(7/3), t^k * tf72f (6/7) t)
      = (32/35)*(7/3)^(k+1)/((k:ℝ)+1) + (-288/343)*(7/3)^(k+3)/((k:ℝ)+3)
        + (864/2401)*(7/3)^(k+4)/((k:ℝ)+4) + (-7776/588245)*(7/3)^(k+6)/((k:ℝ)+6) := by
  set c0 : ℝ := (6/7/30)*32 with hc0
  set c1 : ℝ := (6/7/30)*(-(40*(6/7)^2)) with hc1
  set c2 : ℝ := (6/7/30)*(20*(6/7)^3) with hc2
  set c3 : ℝ := (6/7/30)*(-((6/7)^5)) with hc3
  -- on `[0, 7/3]` the test function is the given polynomial
  have hEq : Set.EqOn (fun t => t^k * tf72f (6/7) t)
      (fun t => t^k * (c0 + c1*t^2 + c2*t^3 + c3*t^5)) (Set.uIcc (0:ℝ) (7/3)) := by
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 7/3)] at ht
    have ht' : t ∈ Set.Icc (0:ℝ) (2/(6/7)) := by
      rw [show (2:ℝ)/(6/7) = 7/3 by norm_num]; exact ht
    rw [tf72f_eq_poly (6/7) (by norm_num) t ht']
    rw [hc0, hc1, hc2, hc3]
    ring
  rw [intervalIntegral.integral_congr hEq]
  rw [tf72f_moment_lin k (7/3) c0 c1 c2 c3]
  rw [hc0, hc1, hc2, hc3]
  exact tf72f_moment_alg k

end Work.ZeroFreeTables
