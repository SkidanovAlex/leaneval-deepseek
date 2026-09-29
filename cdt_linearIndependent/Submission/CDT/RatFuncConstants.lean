import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.Commons.Algebra.Polynomial.eq_C_of_derivative_mul_eq

/-!
# The constants of `K(X)`

A rational function whose derivative vanishes is a constant: `K(X)` has constant field `K`.
This is the `K(X)`-case of the classical fact that the constants of a differential field form a
field; it converts a rational function with vanishing derivative -- such as the coefficients of
the "integrals" in the paper's relation `(todiff)` -- into an element of the constant field.
The polynomial core (`q · p' = p · q'` with `p, q` coprime forces `q` constant) is
`Commons.Algebra.Polynomial.eq_C_of_derivative_mul_eq`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

/-- The image of a constant polynomial in `K(X)`. -/
lemma am_C' {K : Type*} [Field K] (c : K) :
    algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) = algebraMap K (RatFunc K) c := by
  rw [Polynomial.C_eq_algebraMap]
  exact IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) c

/-- **The constants of `K(X)`.**  A rational function with zero derivative is a constant. -/
theorem exists_const_of_dRat_eq_zero {K : Type*} [Field K] [CharZero K] {f : RatFunc K}
    (h : dRat f = 0) : ∃ c : K, f = algebraMap K (RatFunc K) c := by
  have h2 : dRat (algebraMap (Polynomial K) (RatFunc K) f.num
      / algebraMap (Polynomial K) (RatFunc K) f.denom) = 0 := by
    rw [RatFunc.num_div_denom f]
    exact h
  rw [dRat_div] at h2
  have hden : (algebraMap (Polynomial K) (RatFunc K) f.denom) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f))
  have h3 : algebraMap (Polynomial K) (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)
      = algebraMap (Polynomial K) (RatFunc K) 0 := by
    rcases div_eq_zero_iff.mp h2 with hc | hc
    · simpa using hc
    · exact absurd hc hden
  have h4 : f.num.derivative * f.denom - f.num * f.denom.derivative = 0 :=
    RatFunc.algebraMap_injective K h3
  have hmain : f.denom * f.num.derivative = f.num * f.denom.derivative := by
    have h5 : f.num.derivative * f.denom = f.num * f.denom.derivative := sub_eq_zero.mp h4
    rwa [mul_comm f.num.derivative f.denom] at h5
  obtain ⟨c, hc⟩ := Commons.Algebra.Polynomial.eq_C_of_derivative_mul_eq (K := K)
    (p := f.num) (q := f.denom) (RatFunc.isCoprime_num_denom f) hmain
  have hne : c ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0] at hc
    exact RatFunc.denom_ne_zero f hc
  have hnumderiv : f.num.derivative = 0 := by
    have h6 : Polynomial.C c * f.num.derivative = 0 := by
      have h7 := hmain
      rw [hc] at h7
      simpa using h7
    rcases mul_eq_zero.mp h6 with h7 | h7
    · exact absurd h7 (Polynomial.C_ne_zero.mpr hne)
    · exact h7
  set d : K := f.num.coeff 0 with hd
  have hnumconst : f.num = Polynomial.C d := by
    rw [hd]
    exact Polynomial.eq_C_of_derivative_eq_zero hnumderiv
  refine ⟨d / c, ?_⟩
  calc f = algebraMap (Polynomial K) (RatFunc K) f.num
        / algebraMap (Polynomial K) (RatFunc K) f.denom :=
        (RatFunc.num_div_denom f).symm
    _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C d)
        / algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) := by
        rw [hnumconst, hc]
    _ = algebraMap K (RatFunc K) d / algebraMap K (RatFunc K) c := by
        rw [am_C', am_C']
    _ = algebraMap K (RatFunc K) (d / c) := (map_div₀ _ _ _).symm

/-- A rational function is constant iff its derivative vanishes. -/
lemma dRat_eq_zero_iff_exists_const {K : Type*} [Field K] [CharZero K] (f : RatFunc K) :
    dRat f = 0 ↔ ∃ c : K, f = algebraMap K (RatFunc K) c := by
  constructor
  · exact exists_const_of_dRat_eq_zero
  · rintro ⟨c, rfl⟩
    rw [← am_C' c]
    exact dRat_C c

end Submission.CDT
