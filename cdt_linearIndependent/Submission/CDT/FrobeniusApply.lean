import Mathlib
import Submission.CDT.FrobeniusLocal
import Submission.CDT.ElimReductionC
import Submission.Commons.Analysis.Arithmetic.indicial_zero_ne_zero
import Submission.Commons.Analysis.Arithmetic.indicial_four_ne_zero
import Submission.Commons.Analysis.Arithmetic.indicial_neg_inv72_ne_zero

/-!
# The Frobenius analysis of the eliminated operator at the singular points

The eliminated equation (see `Submission.CDT.ElimOpC`) is

`∑_j A_j b3^{(j)} = D1^4 · R`,  `A_j = 2 P_j D1^j` (`j ≤ 3`), `A_4 = -D1^4`.

At each root `α` of `D1` the operator is *Frobenius-regular*: writing
`z = X - C α`, `D1 = z·Q`, every `A_j` is divisible by `z^j`, say `A_j = z^j B_j`
with `B_j(α) ≠ 0`.  Hence the indicial polynomial
`σ_α(N) = ∑_j (N)_j B_j(α)` governs the order of `b3` at `α`: if `σ_α(N) ≠ 0`
then `ord_α(∑_j A_j b3^{(j)}) = ord_α(b3)`.

This module sets up the data at `α = 0` and derives the first pole bound.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace FrobeniusApply

open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC
open Commons.Analysis.Arithmetic

/-- `D1 = X · Q0` at the origin. -/
def Q0 : Polynomial ℂ := 4 - 185 * X - 33450 * X ^ 2 + 42934 * X ^ 3 - 50112 * X ^ 4
  + 10368 * X ^ 5

lemma D1_eq_X_mul_Q0 : D1 = X * Q0 := by unfold D1 Q0 y; ring

lemma Q0_eval_zero : Q0.eval 0 = 4 := by unfold Q0; simp

lemma Q0_ne_zero : Q0 ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℂ => Polynomial.eval 1 p) h
  simp [Q0] at this
  norm_num at this

/-- The Frobenius coefficients at the origin. -/
def Bfun : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * Q0
  | 2 => 2 * P2 * Q0 ^ 2
  | 3 => 2 * P3 * Q0 ^ 3
  | _ => -(Q0 ^ 4)

/-- The polynomial coefficients of the eliminated operator. -/
def Afun : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * D1
  | 2 => 2 * P2 * D1 ^ 2
  | 3 => 2 * P3 * D1 ^ 3
  | _ => -(D1 ^ 4)

lemma Bfun_eq_zero : Bfun 0 = 2 * P0 := rfl
lemma Bfun_eq_one : Bfun 1 = 2 * P1 * Q0 := rfl
lemma Bfun_eq_two : Bfun 2 = 2 * P2 * Q0 ^ 2 := rfl
lemma Bfun_eq_three : Bfun 3 = 2 * P3 * Q0 ^ 3 := rfl
lemma Bfun_eq_four : Bfun 4 = -(Q0 ^ 4) := rfl

lemma Afun_eq_zero : Afun 0 = 2 * P0 := rfl
lemma Afun_eq_one : Afun 1 = 2 * P1 * D1 := rfl
lemma Afun_eq_two : Afun 2 = 2 * P2 * D1 ^ 2 := rfl
lemma Afun_eq_three : Afun 3 = 2 * P3 * D1 ^ 3 := rfl
lemma Afun_eq_four : Afun 4 = -(D1 ^ 4) := rfl

/-- `A_j = X^j · B_j`. -/
lemma A_split : ∀ j ∈ Finset.range 5, Afun j = X ^ j * Bfun j := by
  intro j hj
  simp only [Finset.mem_range] at hj
  interval_cases j <;>
    simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
      Bfun_eq_zero, Bfun_eq_one, Bfun_eq_two, Bfun_eq_three, Bfun_eq_four,
      D1_eq_X_mul_Q0] <;> ring

/-! ## The indicial value at the origin -/

lemma Bfun_eval0 : (Bfun 0).eval 0 = (-14400 : ℂ) := by
  simp only [Bfun_eq_zero, eval_mul, eval_ofNat]
  unfold P0 y
  simp
  norm_num

lemma Bfun_eval1 : (Bfun 1).eval 0 = (12096 : ℂ) := by
  simp only [Bfun_eq_one, eval_mul, eval_pow, eval_ofNat]
  rw [Q0_eval_zero]
  unfold P1 y
  simp
  norm_num

lemma Bfun_eval2 : (Bfun 2).eval 0 = (-4928 : ℂ) := by
  simp only [Bfun_eq_two, eval_mul, eval_pow, eval_ofNat]
  rw [Q0_eval_zero]
  unfold P2 y
  simp
  norm_num

lemma Bfun_eval3 : (Bfun 3).eval 0 = (1280 : ℂ) := by
  simp only [Bfun_eq_three, eval_mul, eval_pow, eval_ofNat]
  rw [Q0_eval_zero]
  unfold P3 y
  simp
  norm_num

lemma Bfun_eval4 : (Bfun 4).eval 0 = (-256 : ℂ) := by
  simp only [Bfun_eq_four, eval_neg, eval_pow]
  rw [Q0_eval_zero]
  norm_num

lemma fallFact1 (N : ℤ) : ((fallFact N 1 : ℤ) : ℂ) = (N : ℂ) := by
  simp only [fallFact, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

lemma fallFact2 (N : ℤ) : ((fallFact N 2 : ℤ) : ℂ) = (N : ℂ) * ((N : ℂ) - 1) := by
  simp only [fallFact, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

lemma fallFact3 (N : ℤ) :
    ((fallFact N 3 : ℤ) : ℂ) = (N : ℂ) * ((N : ℂ) - 1) * ((N : ℂ) - 2) := by
  simp only [fallFact, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

lemma fallFact4 (N : ℤ) :
    ((fallFact N 4 : ℤ) : ℂ) = (N : ℂ) * ((N : ℂ) - 1) * ((N : ℂ) - 2) * ((N : ℂ) - 3) := by
  simp only [fallFact, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

/-- The indicial value at the origin, in terms of the rational indicial polynomial. -/
lemma sigma0_val (N : ℤ) :
    (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Bfun j).eval 0)
      = ((256 : ℚ) : ℂ) * (((-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ)
          + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
          + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
          + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [fallFact_zero, Int.cast_one, one_mul, Bfun_eval0, Bfun_eval1, Bfun_eval2,
    Bfun_eval3, Bfun_eval4, fallFact1, fallFact2, fallFact3, fallFact4]
  push_cast
  ring

/-- The cleared eliminated equation, written as a `Finset.range 5` sum. -/
lemma sum5_expand (b3 : RF) :
    (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3))
      = am (2 * P0) * b3 + am (2 * P1 * D1) * dRat b3
        + am (2 * P2 * D1 ^ 2) * dRat (dRat b3)
        + am (2 * P3 * D1 ^ 3) * dRat (dRat (dRat b3))
        - am (D1 ^ 4) * dRat (dRat (dRat (dRat b3))) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
    Function.iterate_zero_apply, Function.iterate_one, Function.iterate_succ_apply',
    map_neg]
  ring

lemma rootMultiplicity_X_zero : (Polynomial.rootMultiplicity (0 : ℂ) Polynomial.X) = 1 := by
  simpa using Polynomial.rootMultiplicity_X_sub_C_self (x := (0 : ℂ))

lemma rootMultiplicity_Q0_zero : (Polynomial.rootMultiplicity (0 : ℂ) Q0) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_zero]
  intro hroot
  rw [Polynomial.IsRoot, Q0_eval_zero] at hroot
  norm_num at hroot

lemma rootMultiplicity_D1_zero : (Polynomial.rootMultiplicity (0 : ℂ) D1) = 1 := by
  rw [D1_eq_X_mul_Q0, Polynomial.rootMultiplicity_mul (mul_ne_zero Polynomial.X_ne_zero Q0_ne_zero),
    rootMultiplicity_X_zero, rootMultiplicity_Q0_zero, add_zero]

lemma rootMultiplicity_D1pow_zero : (Polynomial.rootMultiplicity (0 : ℂ) (D1 ^ 4)) = 4 := by
  rw [rootMultiplicity_pow' D1 4, rootMultiplicity_D1_zero, mul_one]

lemma D1_pow_ne_zero : (D1 ^ 4 : Polynomial ℂ) ≠ 0 := pow_ne_zero 4 D1_ne_zero

/-- **The local bound at the origin.**  `b3` has no pole at `0`: indeed `ord_0 b3 ≥ 2`. -/
theorem zero_local (b0 b1 b2 b3 R : RF) (hb : b3 ≠ 0) (hR : R ≠ 0)
    (hRlow : (-2 : ℤ) ≤ ordAt (0 : ℂ) R)
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    (2 : ℤ) ≤ ordAt (0 : ℂ) b3 := by
  by_contra hcon
  push_neg at hcon
  set N : ℤ := ordAt (0 : ℂ) b3 with hN
  have hNle : N ≤ 1 := by rw [hN]; omega
  have hnum : b3.num ≠ 0 := RatFunc.num_ne_zero hb
  have hden : b3.denom ≠ 0 := RatFunc.denom_ne_zero b3
  have hrepr : b3 = am b3.num / am b3.denom := (RatFunc.num_div_denom b3).symm
  have hNord : N = (Polynomial.rootMultiplicity (0 : ℂ) b3.num : ℤ)
      - (Polynomial.rootMultiplicity (0 : ℂ) b3.denom : ℤ) := by
    rw [hN]
    conv_lhs => rw [hrepr]
    rw [ordAt_div (0 : ℂ) (RatFunc.algebraMap_ne_zero hnum)
      (RatFunc.algebraMap_ne_zero hden), ordAt_algebraMap, ordAt_algebraMap]
  have hres : ∀ j ∈ Finset.range 5, ((N + 1 : ℤ) : WithTop ℤ)
      ≤ ordAtT (0 : ℂ) (resFun (0 : ℂ) b3 N j) := by
    intro j hj
    rw [hrepr, hNord]
    exact residual_bound hnum hden j
  have hσ : (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Bfun j).eval (0 : ℂ)) ≠ 0 := by
    intro hz
    rw [sigma0_val N] at hz
    have hz' : (((-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ)
        + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
        + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
        + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ)) = 0 := by
      have hq : (((-(225 / 4) : ℚ) + (189 / 4) * (N : ℚ)
          + (-(77 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
          + 5 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
          + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ) : ℂ) = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · norm_num at h
        · exact h
      exact_mod_cast hq
    exact (indicial_zero_ne_zero N hNle) hz'
  have htie := frobenius_tie (K := ℂ) hb (α := (0 : ℂ)) hN.symm (Finset.range 5) Bfun
    (fun j => j) hres hσ
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [sum5_expand]
    exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
  have hsum : (∑ j ∈ Finset.range 5,
      am ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ j * Bfun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [show (Polynomial.X - Polynomial.C (0 : ℂ)) = Polynomial.X from by simp]
    rw [show (∑ j ∈ Finset.range 5, am (Polynomial.X ^ j * Bfun j) * (dRat^[j] b3))
        = ∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3) from
      Finset.sum_congr rfl (fun j hj => by rw [← A_split j hj])]
    exact hEq
  rw [hsum] at htie
  have hval : ordAtT (0 : ℂ) (am (D1 ^ 4) * R) = (((4 + ordAt (0 : ℂ) R) : ℤ) : WithTop ℤ) := by
    rw [ordAtT_mul (0 : ℂ) (RatFunc.algebraMap_ne_zero D1_pow_ne_zero) hR,
      ordAtT_algebraMap D1_pow_ne_zero, rootMultiplicity_D1pow_zero, ordAtT_of_ne hR,
      ← WithTop.coe_add]
    congr 1
  rw [hval, WithTop.coe_eq_coe] at htie
  omega

/-! ## The general tie bound -/

/-- **The general Frobenius tie bound.**  If at `α` all indicial exponents tie
(`Afun j = z^j · B j` with `B j(α) ≠ 0`, i.e. `ord_α(D1) = 1`) and the indicial
value `σ_α(N)` does not vanish for `N ≤ K`, then `ord_α b3 > K`. -/
theorem tie_bound (α : ℂ) (K : ℤ) (z : Polynomial ℂ) (B : ℕ → Polynomial ℂ)
    (b3 R : RF) (hb : b3 ≠ 0) (hR : R ≠ 0)
    (hz : z = Polynomial.X - Polynomial.C α)
    (hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R)
    (hA : ∀ j ∈ Finset.range 5, Afun j = z ^ j * B j)
    (hσ : ∀ N : ℤ, N ≤ K → (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (B j).eval α) ≠ 0)
    (hK : K < (4 * (Polynomial.rootMultiplicity α D1 : ℤ)) + ordAt α R) :
    K < ordAt α b3 := by
  by_contra hcon
  push_neg at hcon
  set N : ℤ := ordAt α b3 with hN
  have hNle : N ≤ K := by rw [hN]; exact hcon
  have hnum : b3.num ≠ 0 := RatFunc.num_ne_zero hb
  have hden : b3.denom ≠ 0 := RatFunc.denom_ne_zero b3
  have hrepr : b3 = am b3.num / am b3.denom := (RatFunc.num_div_denom b3).symm
  have hNord : N = (Polynomial.rootMultiplicity α b3.num : ℤ)
      - (Polynomial.rootMultiplicity α b3.denom : ℤ) := by
    rw [hN]
    conv_lhs => rw [hrepr]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero hnum) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap]
  have hres : ∀ j ∈ Finset.range 5, ((N + 1 : ℤ) : WithTop ℤ)
      ≤ ordAtT α (resFun α b3 N j) := by
    intro j hj
    rw [hrepr, hNord]
    exact residual_bound hnum hden j
  have htie := frobenius_tie (K := ℂ) hb (α := α) hN.symm (Finset.range 5) B (fun j => j)
    hres (hσ N hNle)
  have hsum2 : (∑ j ∈ Finset.range 5,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) ((Polynomial.X - Polynomial.C α) ^ j * B j)
        * (dRat^[j] b3))
      = ∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← hz, ← hA j hj]
  rw [hsum2, hEq] at htie
  have hval : ordAtT α (am (D1 ^ 4) * R)
      = (((4 * (Polynomial.rootMultiplicity α D1 : ℤ)) + ordAt α R : ℤ) : WithTop ℤ) := by
    rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero D1_pow_ne_zero) hR,
      ordAtT_algebraMap D1_pow_ne_zero, rootMultiplicity_pow' D1 4, ordAtT_of_ne hR,
      ← WithTop.coe_add]
    congr 1
  rw [hval, WithTop.coe_eq_coe] at htie
  omega

/-! ## The bound at `α = 4` -/

/-- `D1 = (X - 4)·Q4`. -/
def Q4 : Polynomial ℂ := X * (72 * X + 1) * (144 * X ^ 3 - 122 * X ^ 2 + 118 * X - 1)

lemma X_sub_C_four : (Polynomial.X - Polynomial.C (4 : ℂ) : Polynomial ℂ) = Polynomial.X - 4 := by
  rw [show (Polynomial.C (4 : ℂ) : Polynomial ℂ) = 4 from map_ofNat Polynomial.C 4]

lemma D1_eq_X_sub_four : D1 = (Polynomial.X - Polynomial.C 4) * Q4 := by
  rw [X_sub_C_four]
  unfold D1 Q4 y; ring

lemma Q4_eval_four : Q4.eval 4 = 8941660 := by unfold Q4; norm_num

lemma Q4_ne_zero : Q4 ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℂ => Polynomial.eval 4 p) h
  simp [Q4] at this
  norm_num at this

lemma rootMultiplicity_Q4_four : (Polynomial.rootMultiplicity (4 : ℂ) Q4) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_zero]
  intro hroot
  rw [Polynomial.IsRoot, Q4_eval_four] at hroot
  norm_num at hroot

lemma rootMultiplicity_D1_four : (Polynomial.rootMultiplicity (4 : ℂ) D1) = 1 := by
  rw [D1_eq_X_sub_four,
    Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero 4) Q4_ne_zero),
    Polynomial.rootMultiplicity_X_sub_C_self, rootMultiplicity_Q4_four, add_zero]

def Bfun4 : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * Q4
  | 2 => 2 * P2 * Q4 ^ 2
  | 3 => 2 * P3 * Q4 ^ 3
  | _ => -(Q4 ^ 4)

lemma Bfun4_eq_zero : Bfun4 0 = 2 * P0 := rfl
lemma Bfun4_eq_one : Bfun4 1 = 2 * P1 * Q4 := rfl
lemma Bfun4_eq_two : Bfun4 2 = 2 * P2 * Q4 ^ 2 := rfl
lemma Bfun4_eq_three : Bfun4 3 = 2 * P3 * Q4 ^ 3 := rfl
lemma Bfun4_eq_four : Bfun4 4 = -(Q4 ^ 4) := rfl

lemma A_split_four : ∀ j ∈ Finset.range 5,
    Afun j = (Polynomial.X - Polynomial.C (4 : ℂ)) ^ j * Bfun4 j := by
  intro j hj
  simp only [Finset.mem_range] at hj
  interval_cases j <;>
    simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
      Bfun4_eq_zero, Bfun4_eq_one, Bfun4_eq_two, Bfun4_eq_three, Bfun4_eq_four,
      D1_eq_X_sub_four, X_sub_C_four] <;> ring

lemma Bfun4_eval0 : (Bfun4 0).eval 4 = (-143831869904748991011555600000 : ℂ) := by
  simp only [Bfun4_eq_zero, eval_mul, eval_ofNat]
  unfold P0 y
  simp
  norm_num

lemma Bfun4_eval1 : (Bfun4 1).eval 4 = (134243078577765724944118560000 : ℂ) := by
  simp only [Bfun4_eq_one, eval_mul, eval_pow, eval_ofNat]
  rw [Q4_eval_four]
  unfold P1 y
  simp
  norm_num

lemma Bfun4_eval2 : (Bfun4 2).eval 4 = (-62327143625391229438340760000 : ℂ) := by
  simp only [Bfun4_eq_two, eval_mul, eval_pow, eval_ofNat]
  rw [Q4_eval_four]
  unfold P2 y
  simp
  norm_num

lemma Bfun4_eval3 : (Bfun4 3).eval 4 = (19177582653966532134874080000 : ℂ) := by
  simp only [Bfun4_eq_three, eval_mul, eval_pow, eval_ofNat]
  rw [Q4_eval_four]
  unfold P3 y
  simp
  norm_num

lemma Bfun4_eval4 : (Bfun4 4).eval 4 = (-6392527551322177378291360000 : ℂ) := by
  simp only [Bfun4_eq_four, eval_neg, eval_pow]
  rw [Q4_eval_four]
  norm_num

/-- The indicial value at `4`, in terms of the rational indicial polynomial. -/
lemma sigma4_val (N : ℤ) :
    (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Bfun4 j).eval 4)
      = ((6392527551322177378291360000 : ℂ))
        * (((-(45 / 2) : ℚ) + 21 * (N : ℚ)
          + (-(39 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
          + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
          + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, fallFact_zero, Int.cast_one,
    one_mul, fallFact1, fallFact2, fallFact3, fallFact4, Bfun4_eval0, Bfun4_eval1, Bfun4_eval2,
    Bfun4_eval3, Bfun4_eval4]
  push_cast
  ring

/-- **The local bound at `α = 4`.**  `ord_4 b3 ≥ 2`. -/
theorem four_local (b0 b1 b2 b3 R : RF) (hb : b3 ≠ 0) (hR : R ≠ 0)
    (hRlow : (0 : ℤ) ≤ ordAt (4 : ℂ) R)
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    (2 : ℤ) ≤ ordAt (4 : ℂ) b3 := by
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [sum5_expand]
    exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
  have hσ : ∀ N : ℤ, N ≤ (1 : ℤ) → (∑ j ∈ Finset.range 5,
      (fallFact N j : ℂ) * (Bfun4 j).eval (4 : ℂ)) ≠ 0 := by
    intro N hN hz
    rw [sigma4_val N] at hz
    rcases mul_eq_zero.mp hz with h | h
    · norm_num at h
    · refine (indicial_four_ne_zero N hN) ?_
      exact_mod_cast h
  have hK : (1 : ℤ) < (4 * (Polynomial.rootMultiplicity (4 : ℂ) D1 : ℤ)) + ordAt (4 : ℂ) R := by
    rw [rootMultiplicity_D1_four]
    omega
  have h := tie_bound (4 : ℂ) 1 (Polynomial.X - Polynomial.C (4 : ℂ)) Bfun4 b3 R hb hR rfl hEq
    A_split_four hσ hK
  omega

/-! ## The bound at `α = -1/72` -/

abbrev a72 : ℂ := (((-1 : ℚ) / 72 : ℚ) : ℂ)

def Qm : Polynomial ℂ := 72 * X * (X - 4) * (144 * X ^ 3 - 122 * X ^ 2 + 118 * X - 1)

lemma mul_C_a72 : (72 : Polynomial ℂ) * Polynomial.C (((-1 : ℚ) / 72 : ℚ) : ℂ) = -1 := by
  rw [mul_comm, ← map_ofNat Polynomial.C 72, ← map_mul]
  norm_num

lemma mul_X_sub_C_a72 :
    (72 : Polynomial ℂ) * (Polynomial.X - Polynomial.C (((-1 : ℚ) / 72 : ℚ) : ℂ))
      = 72 * Polynomial.X + 1 := by
  rw [mul_sub, mul_C_a72]
  ring

lemma seventyTwo_ne_zero : (72 : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  simp at hc

lemma D1_eq_m72 : D1 = (Polynomial.X - Polynomial.C (((-1 : ℚ) / 72 : ℚ) : ℂ)) * Qm := by
  have h72 : (72 : Polynomial ℂ) * D1 = (72 * Polynomial.X + 1) * Qm := by
    unfold D1 Qm y; ring
  rw [← mul_X_sub_C_a72, mul_assoc] at h72
  exact mul_left_cancel₀ seventyTwo_ne_zero h72

lemma Qm_eval_ne : Qm.eval a72 ≠ 0 := by
  unfold Qm a72
  norm_num

lemma Qm_ne_zero : Qm ≠ 0 := by
  intro h
  exact Qm_eval_ne (by rw [h]; simp)

lemma rootMultiplicity_Qm_m72 : (Polynomial.rootMultiplicity a72 Qm) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_zero]
  intro hroot
  rw [Polynomial.IsRoot] at hroot
  exact Qm_eval_ne hroot

lemma rootMultiplicity_D1_m72 : (Polynomial.rootMultiplicity a72 D1) = 1 := by
  rw [D1_eq_m72,
    Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero a72) Qm_ne_zero),
    Polynomial.rootMultiplicity_X_sub_C_self, rootMultiplicity_Qm_m72, add_zero]

def Bfun72 : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * Qm
  | 2 => 2 * P2 * Qm ^ 2
  | 3 => 2 * P3 * Qm ^ 3
  | _ => -(Qm ^ 4)

lemma Bfun72_eq_zero : Bfun72 0 = 2 * P0 := rfl
lemma Bfun72_eq_one : Bfun72 1 = 2 * P1 * Qm := rfl
lemma Bfun72_eq_two : Bfun72 2 = 2 * P2 * Qm ^ 2 := rfl
lemma Bfun72_eq_three : Bfun72 3 = 2 * P3 * Qm ^ 3 := rfl
lemma Bfun72_eq_four : Bfun72 4 = -(Qm ^ 4) := rfl

lemma A_split_m72 : ∀ j ∈ Finset.range 5,
    Afun j = (Polynomial.X - Polynomial.C a72) ^ j * Bfun72 j := by
  intro j hj
  simp only [Finset.mem_range] at hj
  interval_cases j <;>
    simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
      Bfun72_eq_zero, Bfun72_eq_one, Bfun72_eq_two, Bfun72_eq_three, Bfun72_eq_four,
      D1_eq_m72] <;> ring

lemma Bfun72_eval0 : (Bfun72 0).eval a72 = (-(989398410206816318208241 : ℂ) / 4211894522952548352) := by
  simp only [Bfun72_eq_zero, eval_mul, eval_ofNat]
  unfold P0 y
  simp
  norm_num

lemma Bfun72_eval1 : (Bfun72 1).eval a72 = ((989398410206816318208241 : ℂ) / 4211894522952548352) := by
  simp only [Bfun72_eq_one, eval_mul, eval_pow, eval_ofNat]
  unfold Qm a72
  norm_num
  unfold P1 y
  norm_num

lemma Bfun72_eval2 : (Bfun72 2).eval a72 = (-(989398410206816318208241 : ℂ) / 8423789045905096704) := by
  simp only [Bfun72_eq_two, eval_mul, eval_pow, eval_ofNat]
  unfold Qm a72
  norm_num
  unfold P2 y
  norm_num

lemma Bfun72_eval3 : (Bfun72 3).eval a72 = ((989398410206816318208241 : ℂ) / 25271367137715290112) := by
  simp only [Bfun72_eq_three, eval_mul, eval_pow, eval_ofNat]
  unfold Qm a72
  norm_num
  unfold P3 y
  norm_num

lemma Bfun72_eval4 : (Bfun72 4).eval a72 = (-(989398410206816318208241 : ℂ) / 75814101413145870336) := by
  simp only [Bfun72_eq_four, eval_neg, eval_pow]
  unfold Qm a72
  norm_num

lemma sigma_m72_val (N : ℤ) :
    (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Bfun72 j).eval a72)
      = ((989398410206816318208241 : ℂ) / 75814101413145870336)
        * (((-18 : ℚ) + 18 * (N : ℚ) + (-9) * ((N : ℚ) * ((N : ℚ) - 1))
          + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
          + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, fallFact_zero, Int.cast_one,
    one_mul, fallFact1, fallFact2, fallFact3, fallFact4, Bfun72_eval0, Bfun72_eval1, Bfun72_eval2,
    Bfun72_eval3, Bfun72_eval4]
  push_cast
  ring

/-- **The local bound at `α = -1/72`.**  `ord_{-1/72} b3 ≥ 1`. -/
theorem m72_local (b0 b1 b2 b3 R : RF) (hb : b3 ≠ 0) (hR : R ≠ 0)
    (hRlow : (0 : ℤ) ≤ ordAt a72 R)
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    (1 : ℤ) ≤ ordAt a72 b3 := by
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [sum5_expand]
    exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
  have hσ : ∀ N : ℤ, N ≤ (0 : ℤ) → (∑ j ∈ Finset.range 5,
      (fallFact N j : ℂ) * (Bfun72 j).eval a72) ≠ 0 := by
    intro N hN hz
    rw [sigma_m72_val N] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (by norm_num)
    · refine (indicial_neg_inv72_ne_zero N hN) ?_
      exact_mod_cast h
  have hK : (0 : ℤ) < (4 * (Polynomial.rootMultiplicity a72 D1 : ℤ)) + ordAt a72 R := by
    rw [rootMultiplicity_D1_m72]
    omega
  have h := tie_bound a72 0 (Polynomial.X - Polynomial.C a72) Bfun72 b3 R hb hR rfl hEq
    A_split_m72 hσ hK
  omega

end FrobeniusApply

end Submission.CDT
