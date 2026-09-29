import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.RatFunc.Basic
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_one
import Submission.Commons.FieldTheory.RatFunc.ordAt_zero

namespace Commons.FieldTheory.RatFunc

open Polynomial

/-- `rootMultiplicity` is additive over a power of a nonzero polynomial. -/
private theorem rootMultiplicity_pow {K : Type*} [Field K] (α : K) {p : Polynomial K}
    (hp : p ≠ 0) (n : ℕ) : (p ^ n).rootMultiplicity α = n * p.rootMultiplicity α := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]
    ring

/-- If `x.num * q = p * x.denom` with `p, q` nonzero, then the order of vanishing of `x` at `α`
is the root multiplicity of `p` minus the root multiplicity of `q`. -/
private theorem ordAt_of_num_denom {K : Type*} [Field K] (α : K) {x : RatFunc K} (hx : x ≠ 0)
    {p q : Polynomial K} (hp : p ≠ 0) (hq : q ≠ 0) (h : x.num * q = p * x.denom) :
    ordAt α x = (p.rootMultiplicity α : ℤ) - (q.rootMultiplicity α : ℤ) := by
  have hxnum : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hrm := congrArg (Polynomial.rootMultiplicity α) h
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hxnum hq),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hp (RatFunc.denom_ne_zero x))] at hrm
  have hZ : (x.num.rootMultiplicity α : ℤ) + (q.rootMultiplicity α : ℤ)
      = (p.rootMultiplicity α : ℤ) + (x.denom.rootMultiplicity α : ℤ) := by
    exact_mod_cast hrm
  rw [ordAt_def]
  linarith

/-- The order of vanishing of a power is the multiple of the order. -/
theorem ordAt_pow {K : Type*} [Field K] (α : K) (x : RatFunc K) (n : ℕ) :
    ordAt α (x ^ n) = n * ordAt α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, pow_zero, ordAt_one]; simp
    · rw [zero_pow hn.ne', ordAt_zero]; simp
  · have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx
    have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
    have hq : x.denom ^ n ≠ 0 := pow_ne_zero n hden
    have hdiv : x ^ n = algebraMap (Polynomial K) (RatFunc K) (x.num ^ n)
        / algebraMap (Polynomial K) (RatFunc K) (x.denom ^ n) := by
      conv_lhs => rw [← RatFunc.num_div_denom x]
      rw [div_pow, ← map_pow, ← map_pow]
    have hrel : (x ^ n).num * x.denom ^ n = x.num ^ n * (x ^ n).denom :=
      (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hdiv
    have hmain := ordAt_of_num_denom α (pow_ne_zero n hx) (pow_ne_zero n hnum) hq hrel
    rw [hmain, rootMultiplicity_pow α hnum n, rootMultiplicity_pow α hden n, ordAt_def]
    push_cast
    ring

end Commons.FieldTheory.RatFunc
