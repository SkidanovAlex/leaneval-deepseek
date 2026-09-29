import Mathlib
import Submission.Work.C7.xdefs

/-!
# `Work.C7.rat_ode2` — two more rational ODEs with no rational solution

Both statements are instances of the elementary obstruction for a rational function to be a
derivative (`Submission.CDT.ordAt_dRat_ne_neg_one`: `dRat g` never has a *simple* pole):

* **First equation.**  `2 (X-2)² / (X-1)²` has a double pole at `X = 1`, so if `dRat δ` equalled
  it then `δ` would have a simple pole there; adding the simple pole `-2/(X-1)` (whose derivative is
  `2/(X-1)²`) cancels the double pole and exhibits
  `dRat (δ + 2/(X-1)) = 2(X-3)/(X-1)`, which has a simple pole at `X = 1` — impossible.
* **Second equation.**  `(X-2)/(X(X-1))` already has a simple pole at `X = 0`
  (`ordAt 0 = -1`), which no derivative has.
-/

namespace Work.C7

open Polynomial

/-- `X - c` as the image of the polynomial `X - C c`. -/
lemma Xq_sub_C_eq' (c : ℚ) : ((RatFunc.X : RatFunc ℚ) - RatFunc.C c)
    = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C c) := by
  rw [show RatFunc.C c = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl,
      ← RatFunc.algebraMap_X, ← map_sub]

/-- `X - c` is a non-zero rational function. -/
lemma Xq_sub_C_ne (c : ℚ) : ((RatFunc.X : RatFunc ℚ) - RatFunc.C c) ≠ 0 := by
  rw [Xq_sub_C_eq' c]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)

/-- **The order of vanishing of `X - c` at `a`** is `1` exactly at `a = c` and `0` elsewhere. -/
lemma ordAt_Xq_sub_C' (a c : ℚ) :
    Submission.CDT.ordAt a ((RatFunc.X : RatFunc ℚ) - RatFunc.C c) = if a = c then 1 else 0 := by
  rw [Xq_sub_C_eq' c, Submission.CDT.ordAt_algebraMap, Polynomial.rootMultiplicity_X_sub_C]
  split_ifs <;> norm_num

/-- **The order of vanishing of a constant is zero.** -/
lemma ordAt_ratC (a c : ℚ) : Submission.CDT.ordAt a (RatFunc.C c) = 0 := by
  rw [show RatFunc.C c = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl,
    Submission.CDT.ordAt_algebraMap, Polynomial.rootMultiplicity_C, Nat.cast_zero]

lemma Xq_sub_one_eq : ((RatFunc.X : RatFunc ℚ) - 1)
    = ((RatFunc.X : RatFunc ℚ) - RatFunc.C (1:ℚ)) := by norm_num

lemma Xq_sub_two_eq : ((RatFunc.X : RatFunc ℚ) - 2)
    = ((RatFunc.X : RatFunc ℚ) - RatFunc.C (2:ℚ)) := by norm_num

lemma Xq_sub_three_eq : ((RatFunc.X : RatFunc ℚ) - 3)
    = ((RatFunc.X : RatFunc ℚ) - RatFunc.C (3:ℚ)) := by norm_num

lemma ratC_two_eq : (2 : RatFunc ℚ) = RatFunc.C (2:ℚ) := by norm_num

/-- The order of vanishing of `X` at `0` is `1`. -/
lemma ordAt_zero_Xq : Submission.CDT.ordAt (0:ℚ) (RatFunc.X : RatFunc ℚ) = 1 := by
  rw [show (RatFunc.X : RatFunc ℚ) = ((RatFunc.X : RatFunc ℚ) - RatFunc.C (0:ℚ)) from by
        rw [map_zero, sub_zero],
      ordAt_Xq_sub_C' 0 0]
  norm_num

lemma ordAt_one_two : Submission.CDT.ordAt (1:ℚ) (2 : RatFunc ℚ) = 0 := by
  rw [ratC_two_eq, ordAt_ratC 1 2]

lemma ordAt_one_Xq_sub_three : Submission.CDT.ordAt (1:ℚ) ((RatFunc.X : RatFunc ℚ) - 3) = 0 := by
  rw [Xq_sub_three_eq, ordAt_Xq_sub_C' 1 3]; norm_num

lemma ordAt_one_Xq_sub_one : Submission.CDT.ordAt (1:ℚ) ((RatFunc.X : RatFunc ℚ) - 1) = 1 := by
  rw [Xq_sub_one_eq, ordAt_Xq_sub_C' 1 1]; norm_num

lemma dRat_Xq : Submission.CDT.dRat (RatFunc.X : RatFunc ℚ) = 1 := by
  rw [← RatFunc.algebraMap_X, Submission.CDT.dRat_algebraMap, Polynomial.derivative_X, map_one]

lemma dRat_two : Submission.CDT.dRat (2 : RatFunc ℚ) = 0 := by
  rw [ratC_two_eq]
  exact Submission.CDT.dRat_C (2:ℚ)

lemma dRat_Xq_sub_one : Submission.CDT.dRat ((RatFunc.X : RatFunc ℚ) - 1) = 1 := by
  rw [Submission.CDT.dRat_sub, dRat_Xq, Submission.CDT.dRat_one, sub_zero]

/-- The derivative of an inverse: `(f⁻¹)' = -f'/f²`. -/
lemma dRat_inv_rat (f : RatFunc ℚ) (hf : f ≠ 0) :
    Submission.CDT.dRat f⁻¹ = -(Submission.CDT.dRat f) / f^2 := by
  have h := Submission.CDT.dRat_mul f f⁻¹
  rw [mul_inv_cancel₀ hf, Submission.CDT.dRat_one] at h
  have h2 : f * Submission.CDT.dRat f⁻¹ = -(Submission.CDT.dRat f * f⁻¹) :=
    eq_neg_of_add_eq_zero_right h.symm
  rw [eq_div_iff (pow_ne_zero 2 hf)]
  calc Submission.CDT.dRat f⁻¹ * f ^ 2 = f * Submission.CDT.dRat f⁻¹ * f := by ring
    _ = (-(Submission.CDT.dRat f * f⁻¹)) * f := by rw [h2]
    _ = -(Submission.CDT.dRat f) := by field_simp

/-- The derivative of the simple pole `2/(X-1)`. -/
lemma dRat_correction :
    Submission.CDT.dRat (2 * ((RatFunc.X : RatFunc ℚ) - 1)⁻¹)
      = -2 * (((RatFunc.X : RatFunc ℚ) - 1)⁻¹)^2 := by
  have hne1 : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by rw [Xq_sub_one_eq]; exact Xq_sub_C_ne 1
  rw [Submission.CDT.dRat_mul, dRat_two, dRat_inv_rat _ hne1, dRat_Xq_sub_one,
    zero_mul, zero_add, inv_pow, div_eq_mul_inv]
  ring

/-- The algebraic identity behind the first equation: adding the derivative of the simple pole
`2/(X-1)` to `2(X-2)²/(X-1)²` cancels the double pole, leaving the simple pole `2(X-3)/(X-1)`. -/
lemma rat_ode2_key :
    2 * ((RatFunc.X : RatFunc ℚ) - 2) ^ 2 * (((RatFunc.X : RatFunc ℚ) - 1) ^ 2)⁻¹
        + -2 * (((RatFunc.X : RatFunc ℚ) - 1)⁻¹) ^ 2
      = 2 * ((RatFunc.X : RatFunc ℚ) - 3) * ((RatFunc.X : RatFunc ℚ) - 1)⁻¹ := by
  have hne1 : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by rw [Xq_sub_one_eq]; exact Xq_sub_C_ne 1
  rw [inv_pow]
  field_simp
  ring

theorem rat_ode2 :
    (∀ δ : RatFunc ℚ,
        Submission.CDT.dRat δ ≠ 2 * (RatFunc.X - 2) ^ 2 * ((RatFunc.X - 1) ^ 2)⁻¹) ∧
    (∀ δ : RatFunc ℚ,
        Submission.CDT.dRat δ ≠ (RatFunc.X - 2) * (RatFunc.X * (RatFunc.X - 1))⁻¹) := by
  constructor
  · -- `dRat δ = 2(X-2)²/(X-1)²` is impossible: `δ + 2/(X-1)` would have derivative
    -- `2(X-3)/(X-1)`, a simple pole at `X = 1`.
    intro δ h
    have hne1 : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by rw [Xq_sub_one_eq]; exact Xq_sub_C_ne 1
    have hd : Submission.CDT.dRat (δ + 2 * ((RatFunc.X : RatFunc ℚ) - 1)⁻¹)
        = 2 * ((RatFunc.X : RatFunc ℚ) - 3) * ((RatFunc.X : RatFunc ℚ) - 1)⁻¹ := by
      rw [Submission.CDT.dRat_add, h, dRat_correction]
      exact rat_ode2_key
    refine Submission.CDT.ordAt_dRat_ne_neg_one (1 : ℚ)
      (δ + 2 * ((RatFunc.X : RatFunc ℚ) - 1)⁻¹) ?_
    rw [hd]
    have h2ne : (2 : RatFunc ℚ) ≠ 0 := by norm_num
    have hX3 : ((RatFunc.X : RatFunc ℚ) - 3) ≠ 0 := by rw [Xq_sub_three_eq]; exact Xq_sub_C_ne 3
    have h2X3 : (2 : RatFunc ℚ) * ((RatFunc.X : RatFunc ℚ) - 3) ≠ 0 := mul_ne_zero h2ne hX3
    have hinv : ((RatFunc.X : RatFunc ℚ) - 1)⁻¹ ≠ 0 := inv_ne_zero hne1
    rw [Submission.CDT.ordAt_mul 1 h2X3 hinv, Submission.CDT.ordAt_mul 1 h2ne hX3,
        Submission.CDT.ordAt_inv 1 hne1, ordAt_one_two, ordAt_one_Xq_sub_three,
        ordAt_one_Xq_sub_one]
    norm_num
  · -- `dRat δ = (X-2)/(X(X-1))` is impossible: the right-hand side has a simple pole at `X = 0`.
    intro δ h
    refine Submission.CDT.ordAt_dRat_ne_neg_one (0 : ℚ) δ ?_
    rw [h]
    have hX2 : ((RatFunc.X : RatFunc ℚ) - 2) ≠ 0 := by rw [Xq_sub_two_eq]; exact Xq_sub_C_ne 2
    have hX1 : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by rw [Xq_sub_one_eq]; exact Xq_sub_C_ne 1
    have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    have hprod : (RatFunc.X : RatFunc ℚ) * ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 :=
      mul_ne_zero hX hX1
    rw [Submission.CDT.ordAt_mul 0 hX2 (inv_ne_zero hprod), Submission.CDT.ordAt_inv 0 hprod,
        Submission.CDT.ordAt_mul 0 hX hX1, ordAt_zero_Xq,
        Xq_sub_two_eq, Xq_sub_one_eq, ordAt_Xq_sub_C' 0 2, ordAt_Xq_sub_C' 0 1]
    norm_num

end Work.C7
