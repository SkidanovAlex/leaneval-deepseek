import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_zero

namespace Commons.FieldTheory.RatFunc

/-- Elementary arithmetic fact: knowing `min (A + D) (B + C) ≤ M` gives the `min` lower bound
for the corresponding difference. -/
private lemma int_min_sub_le {A B C D M : ℤ} (h : min (A + D) (B + C) ≤ M) :
    min (A - B) (C - D) ≤ M - B - D := by
  rw [min_le_iff] at h ⊢
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- The `min` lower bound: the order of vanishing of a sum is at least the smaller of the two
orders.  (Use `Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt` and
`Polynomial.rootMultiplicity_mul`.) -/
theorem min_ordAt_le_ordAt_add {K : Type*} [Field K] (α : K) {x y : RatFunc K}
    (hxy : x + y ≠ 0) :
    min (ordAt α x) (ordAt α y) ≤ ordAt α (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add]
    simp [ordAt_zero]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
    simp [ordAt_zero]
  have hxn : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hyn : y.num ≠ 0 := RatFunc.num_ne_zero hy
  have hxd : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hyd : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hN : x.num * y.denom + x.denom * y.num ≠ 0 :=
    RatFunc.num_mul_denom_add_denom_mul_num_ne_zero hxy
  -- The polynomial-level `min` bound on the numerator of the sum.
  have hminN : min (x.num.rootMultiplicity α + y.denom.rootMultiplicity α)
        (x.denom.rootMultiplicity α + y.num.rootMultiplicity α)
      ≤ (x.num * y.denom + x.denom * y.num).rootMultiplicity α := by
    have h := Polynomial.rootMultiplicity_add α hN
    rwa [Polynomial.rootMultiplicity_mul (mul_ne_zero hxn hyd),
        Polynomial.rootMultiplicity_mul (mul_ne_zero hxd hyn)] at h
  have hminZ : min ((x.num.rootMultiplicity α : ℤ) + (y.denom.rootMultiplicity α : ℤ))
        ((x.denom.rootMultiplicity α : ℤ) + (y.num.rootMultiplicity α : ℤ))
      ≤ ((x.num * y.denom + x.denom * y.num).rootMultiplicity α : ℤ) := by
    exact_mod_cast hminN
  -- The cross-multiplication identity for the numerator/denominator of `x + y`.
  have key := congrArg (Polynomial.rootMultiplicity α) (RatFunc.num_denom_add x y)
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hxy)
          (mul_ne_zero hxd hyd)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hxd hyd),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hN (RatFunc.denom_ne_zero (x + y)))] at key
  have keyZ : ((x + y).num.rootMultiplicity α : ℤ)
        + ((x.denom.rootMultiplicity α : ℤ) + (y.denom.rootMultiplicity α : ℤ))
      = ((x.num * y.denom + x.denom * y.num).rootMultiplicity α : ℤ)
        + ((x + y).denom.rootMultiplicity α : ℤ) := by
    exact_mod_cast key
  have hxy_ord : ordAt α (x + y)
      = ((x.num * y.denom + x.denom * y.num).rootMultiplicity α : ℤ)
        - (x.denom.rootMultiplicity α : ℤ) - (y.denom.rootMultiplicity α : ℤ) := by
    rw [ordAt_def]
    linarith
  rw [hxy_ord, ordAt_def, ordAt_def]
  exact int_min_sub_le hminZ

end Commons.FieldTheory.RatFunc