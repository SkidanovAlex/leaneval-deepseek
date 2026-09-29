import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt

namespace Commons.FieldTheory.RatFunc

open Polynomial

/-- The multiplicity of `α` as a root of a polynomial is invariant under negation. -/
private theorem rootMultiplicity_neg_eq {K : Type*} [Field K] (α : K) {p : Polynomial K}
    (hp : p ≠ 0) : (-p).rootMultiplicity α = p.rootMultiplicity α := by
  have hC : (Polynomial.C (-1 : K)) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; norm_num
  have hneg : (-p) = Polynomial.C (-1 : K) * p := by
    rw [Polynomial.C_neg, Polynomial.C_1]; ring
  rw [hneg, Polynomial.rootMultiplicity_mul (mul_ne_zero hC hp), Polynomial.rootMultiplicity_C,
    zero_add]

/-- If `u.num * q = p * u.denom` — i.e. `u` is represented by the cross-multiplied fraction
`p / q` — with `p, q` nonzero polynomials, then the order of vanishing of `u` at `α` equals
`rootMultiplicity α p - rootMultiplicity α q`. -/
theorem ordAt_of_num_mul_denom_eq {K : Type*} [Field K] (α : K) {u : RatFunc K}
    {p q : Polynomial K} (h : u.num * q = p * u.denom) (hp : p ≠ 0) (hq : q ≠ 0) :
    ordAt α u = (p.rootMultiplicity α : ℤ) - (q.rootMultiplicity α : ℤ) := by
  have hden : u.denom ≠ 0 := RatFunc.denom_ne_zero u
  have hnum : u.num ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    rcases mul_eq_zero.mp h.symm with hp0 | hd0
    · exact hp hp0
    · exact hden hd0
  have key := congrArg (fun r : Polynomial K => r.rootMultiplicity α) h
  rw [Polynomial.rootMultiplicity_mul (p := u.num) (q := q) (x := α) (mul_ne_zero hnum hq),
      Polynomial.rootMultiplicity_mul (p := p) (q := u.denom) (x := α)
        (mul_ne_zero hp hden)] at key
  rw [ordAt_def]
  have keyZ : (u.num.rootMultiplicity α : ℤ) + (q.rootMultiplicity α : ℤ)
      = (p.rootMultiplicity α : ℤ) + (u.denom.rootMultiplicity α : ℤ) := by
    exact_mod_cast key
  linarith

/-- Strict dominance: if `x` vanishes to strictly lower order than `y` at `α`, then `x + y` has
the order of vanishing of `x`. -/
theorem ordAt_add_of_lt {K : Type*} [Field K] (α : K) {x y : RatFunc K} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : ordAt α x < ordAt α y) : ordAt α (x + y) = ordAt α x := by
  have hxN : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hyN : y.num ≠ 0 := RatFunc.num_ne_zero hy
  have hxD : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hyD : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hPne : x.num * y.denom ≠ 0 := mul_ne_zero hxN hyD
  have hQne : x.denom * y.num ≠ 0 := mul_ne_zero hxD hyN
  have hDne : x.denom * y.denom ≠ 0 := mul_ne_zero hxD hyD
  -- The strict inequality of orders, as an inequality of sums of root multiplicities.
  have hltZ : ((x.num.rootMultiplicity α : ℤ) + (y.denom.rootMultiplicity α : ℤ))
      < ((x.denom.rootMultiplicity α : ℤ) + (y.num.rootMultiplicity α : ℤ)) := by
    rw [ordAt_def, ordAt_def] at h
    linarith
  have hlt : (x.num * y.denom).rootMultiplicity α < (x.denom * y.num).rootMultiplicity α := by
    rw [Polynomial.rootMultiplicity_mul (p := x.num) (q := y.denom) (x := α) hPne,
        Polynomial.rootMultiplicity_mul (p := x.denom) (q := y.num) (x := α) hQne]
    exact_mod_cast hltZ
  -- The cross-multiplied numerator of `x + y` is nonzero: otherwise `x = -y`.
  have hAne : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro hzero
    have hPQ : x.num * y.denom = -(x.denom * y.num) := eq_neg_of_add_eq_zero_left hzero
    have hrmeq : (x.num * y.denom).rootMultiplicity α
        = (x.denom * y.num).rootMultiplicity α := by
      rw [hPQ, rootMultiplicity_neg_eq α hQne]
    exact absurd hrmeq (ne_of_lt hlt)
  -- The root multiplicity of the cross-multiplied numerator is that of `x.num * y.denom`.
  have hrm : (x.num * y.denom + x.denom * y.num).rootMultiplicity α
      = (x.num * y.denom).rootMultiplicity α :=
    Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt hPne hlt
  have hnumdenom := RatFunc.num_denom_add x y
  have hord := ordAt_of_num_mul_denom_eq α hnumdenom hAne hDne
  rw [hord, hrm, ordAt_def,
      Polynomial.rootMultiplicity_mul (p := x.num) (q := y.denom) (x := α) hPne,
      Polynomial.rootMultiplicity_mul (p := x.denom) (q := y.denom) (x := α) hDne]
  push_cast
  ring

end Commons.FieldTheory.RatFunc