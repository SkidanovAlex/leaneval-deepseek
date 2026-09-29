import Submission.CDT.LogUnlikelyG
import Submission.Commons.RingTheory.PowerSeries.coeff_LHS_general

/-!
# The `M`-identities of the Theorem-C route (paper §"The overconvergent space")

This module proves the three identities of CDT (arXiv:2408.15403),
§"The overconvergent space", second display:

```lean
M(H(a) ⋆ A(b)) = −b + 3aX − 3bX² + aX³,
M(A(a) ⋆ H(b)) = −a + 3bX − 3aX² + bX³,
M(H(a) ⋆ H(b)) = −1 + 2X² − X⁴,
```

where `M = logPAODE a b` is the paper's order-two operator `(ODE)`
(`LogHadamard.logPA_ode` is the case `M(A(a) ⋆ A(b)) = 0`), and their
consequence that the unlikely `G`-function `P` of `LogUnlikelyG` satisfies an
*inhomogeneous* ODE with polynomial right-hand side (`logP_ode` below).

**Method.**  The coefficient sequences `uₙ(a)`, `vₙ(a)` of `A(a,x)`,
`H(a,x)` both satisfy the three-term Legendre recurrence `RecProp`
(`beukersU_homogeneous`/`beukersV_homogeneous`), and the certificate
`Commons.RingTheory.PowerSeries.coeff_LHS_general` shows that for *any* such
pair `(f, g)` the `xⁿ`-coefficient (`n ≥ 7`) of the operator applied to the
Hadamard product `mk (fun m => f m · g m)` vanishes.  Hence the three series
`M(mk (v·u))`, `M(mk (u·v))`, `M(mk (v·v))` are *polynomials of degree ≤ 6*;
their seven small coefficients are computed here explicitly from the first
nine values of `u` and `v` (`norm_num`/`ring`).  (Numerically checked:
`Scratch/lemma14/logM_check.py`.)

Linearity in the series argument then gives `logP_ode`: the rational
unlikely function `logP` (whose coefficients are, under the relation (rabc),
those of `r_a·P_a + r_b·P_b + r_ab·P_ab` — `LogUnlikelyG.logPCoeff_eq_rat`)
satisfies `M(logP) = r_a(−b + 3aX − 3bX² + aX³) + r_b(−a + 3bX − 3aX² + bX³)
+ r_ab(−1 + 2X² − X⁴) ∈ ℚ[X]`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open PowerSeries

namespace Submission.CDT

noncomputable section

/-! ## The three-term recurrences -/

/-- `usum = logPAU = beukersU` (the binomial-sum sequence). -/
lemma usum_eq_beukersU (t : ℚ) (m : ℕ) :
    Commons.RingTheory.PowerSeries.usum t m = beukersU t m := by
  rw [show Commons.RingTheory.PowerSeries.usum t m = logPAU t m from rfl, logPAU_eq_beukersU]

/-- The Beukers sequence `uₙ(a)` satisfies the three-term recurrence. -/
lemma RecProp_beukersU (a : ℚ) :
    Commons.RingTheory.PowerSeries.RecProp a (fun n => beukersU a n) := by
  have h := Commons.RingTheory.PowerSeries.RecProp_usum a
  have hfun : (fun n => Commons.RingTheory.PowerSeries.usum a n) = (fun n => beukersU a n) := by
    funext m
    exact usum_eq_beukersU a m
  simpa [hfun] using h

/-- The companion Beukers sequence `vₙ(a)` satisfies the same three-term
recurrence (`beukersV_homogeneous`). -/
lemma RecProp_beukersV (a : ℚ) :
    Commons.RingTheory.PowerSeries.RecProp a (fun n => beukersV a n) := by
  intro N j
  have hn : 1 ≤ N + j + 1 := by omega
  have h := beukersV_homogeneous a hn
  rw [eq_div_iff (by positivity : (((N + j + 1 : ℕ) : ℚ) + 1) ≠ 0)]
  have h1 : N + j + 1 + 1 = N + j + 2 := by omega
  have h2 : N + j + 1 - 1 = N + j := by omega
  rw [h1, h2] at h
  simpa [mul_comm, mul_assoc, mul_left_comm] using h

/-! ## Coefficient extraction for a general series -/

/-- Coefficient of `C c · X^d · Y`. -/
lemma coeff_C_pow_mul_gen (c : ℚ) (Y : PowerSeries ℚ) (n d : ℕ) :
    PowerSeries.coeff n (PowerSeries.C c * PowerSeries.X ^ d * Y)
      = if d ≤ n then c * PowerSeries.coeff (n - d) Y else 0 := by
  by_cases h : d ≤ n
  · rw [if_pos h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul _ n d h]
  · rw [if_neg h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul_of_lt _ n d (by omega)]
    simp

/-- Coefficient of `C c · X^d · Y′`. -/
lemma coeff_C_pow_deriv_gen (c : ℚ) (Y : PowerSeries ℚ) (n d : ℕ) :
    PowerSeries.coeff n (PowerSeries.C c * PowerSeries.X ^ d * PowerSeries.derivative (R := ℚ) Y)
      = if d ≤ n then c * ((n - d + 1 : ℕ) : ℚ) * PowerSeries.coeff ((n - d) + 1) Y else 0 := by
  by_cases h : d ≤ n
  · rw [if_pos h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul _ n d h, PowerSeries.coeff_derivative]
    push_cast
    ring
  · rw [if_neg h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul_of_lt _ n d (by omega)]
    simp

/-- Coefficient of `C c · X^d · Y″`. -/
lemma coeff_C_pow_deriv2_gen (c : ℚ) (Y : PowerSeries ℚ) (n d : ℕ) :
    PowerSeries.coeff n (PowerSeries.C c * PowerSeries.X ^ d
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y))
      = if d ≤ n then c * (((n - d + 1) * (n - d + 2) : ℕ) : ℚ) * PowerSeries.coeff ((n - d) + 2) Y
        else 0 := by
  by_cases h : d ≤ n
  · rw [if_pos h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul _ n d h,
      Commons.RingTheory.PowerSeries.coeff_der2]
    push_cast
    ring
  · rw [if_neg h, mul_assoc, Commons.RingTheory.PowerSeries.coeff_C_mul,
      Commons.RingTheory.PowerSeries.coeff_X_pow_mul_of_lt _ n d (by omega)]
    simp

/-! ## The three M-identities -/

/-- the coefficient sequence `vₙ(a)·uₙ(b)` of `H(a) ⋆ A(b)` -/
def Yvu (a b : ℚ) : PowerSeries ℚ := PowerSeries.mk (fun m => beukersV a m * beukersU b m)

/-- the coefficient sequence `uₙ(a)·vₙ(b)` of `A(a) ⋆ H(b)` -/
def Yuv (a b : ℚ) : PowerSeries ℚ := PowerSeries.mk (fun m => beukersU a m * beukersV b m)

/-- the coefficient sequence `vₙ(a)·vₙ(b)` of `H(a) ⋆ H(b)` -/
def Yvv (a b : ℚ) : PowerSeries ℚ := PowerSeries.mk (fun m => beukersV a m * beukersV b m)

/-! ## Values of the Beukers sequences `uₙ(a)` (up to `n = 8`) -/

lemma beukersV_eval2 (a : ℚ) : beukersV a 2 = 3 * a / 2 := beukersV_two a

lemma beukersV_eval3 (a : ℚ) : beukersV a 3 = (15 * a ^ 2 - 4) / 6 := beukersV_three a

lemma beukersU_eval3 (a : ℚ) : beukersU a 3 = (5 * a ^ 3 - 3 * a) / 2 := by
  rw [← usum_eq_beukersU a 3, Commons.RingTheory.PowerSeries.usum_eval3]

lemma beukersU_eval4 (a : ℚ) : beukersU a 4 = (35 * a ^ 4 - 30 * a ^ 2 + 3) / 8 := by
  rw [← usum_eq_beukersU a 4, Commons.RingTheory.PowerSeries.usum_eval4]

lemma beukersU_eval5 (a : ℚ) : beukersU a 5 = (63 * a ^ 5 - 70 * a ^ 3 + 15 * a) / 8 := by
  rw [← usum_eq_beukersU a 5, Commons.RingTheory.PowerSeries.usum_eval5]

lemma beukersU_eval6 (a : ℚ) : beukersU a 6 = (231 * a ^ 6 - 315 * a ^ 4 + 105 * a ^ 2 - 5) / 16 := by
  rw [← usum_eq_beukersU a 6, Commons.RingTheory.PowerSeries.usum_eval6]

lemma beukersU_eval7 (a : ℚ) : beukersU a 7 = (429 * a ^ 7 - 693 * a ^ 5 + 315 * a ^ 3 - 35 * a) / 16 := by
  rw [← usum_eq_beukersU a 7, Commons.RingTheory.PowerSeries.usum_eval7]

lemma beukersU_eval8 (a : ℚ) :
    beukersU a 8 = (6435 * a ^ 8 - 12012 * a ^ 6 + 6930 * a ^ 4 - 1260 * a ^ 2 + 35) / 128 := by
  have h := beukersU_step a 6
  norm_num at h
  rw [beukersU_eval6, beukersU_eval7] at h
  field_simp at h ⊢
  nlinarith


/-! ## Values of the companion sequence `vₙ(a)` (up to `n = 8`) -/

lemma beukersV_eval4 (a : ℚ) : beukersV a 4 = 5 * a * (21 * a ^ 2 - 11) / 24 := by
  have h := beukersV_step a 2
  norm_num at h
  rw [beukersV_eval2, beukersV_eval3] at h
  field_simp at h ⊢
  nlinarith

lemma beukersV_eval5 (a : ℚ) : beukersV a 5 = (945 * a ^ 4 - 735 * a ^ 2 + 64) / 120 := by
  have h := beukersV_step a 3
  norm_num at h
  rw [beukersV_eval3, beukersV_eval4] at h
  field_simp at h ⊢
  nlinarith

lemma beukersV_eval6 (a : ℚ) : beukersV a 6 = 7 * a * (165 * a ^ 4 - 170 * a ^ 2 + 33) / 80 := by
  have h := beukersV_step a 4
  norm_num at h
  rw [beukersV_eval4, beukersV_eval5] at h
  field_simp at h ⊢
  nlinarith

lemma beukersV_eval7 (a : ℚ) : beukersV a 7 = (15015 * a ^ 6 - 19250 * a ^ 4 + 5943 * a ^ 2 - 256) / 560 := by
  have h := beukersV_step a 5
  norm_num at h
  rw [beukersV_eval5, beukersV_eval6] at h
  field_simp at h ⊢
  nlinarith

lemma beukersV_eval8 (a : ℚ) : beukersV a 8 = a * (225225 * a ^ 6 - 345345 * a ^ 4 + 147455 * a ^ 2 - 15159) / 4480 := by
  have h := beukersV_step a 6
  norm_num at h
  rw [beukersV_eval6, beukersV_eval7] at h
  field_simp at h ⊢
  nlinarith

/-! ## The small coefficients `n ≤ 6` -/

/-- The coefficients `n ≤ 6` of the operator applied to `mk (f·g)`, for the
pair `vu`. -/
theorem coeff_LHS_vu_small (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b)))
      + Commons.RingTheory.PowerSeries.P1fac a b * (PowerSeries.derivative (R := ℚ) (Yvu a b)) + Commons.RingTheory.PowerSeries.P0fac a b * (Yvu a b))
      = (if n = 0 then -b else if n = 1 then 3 * a else if n = 2 then -(3 * b)
          else if n = 3 then a else if n = 4 then 0 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · rw [Commons.RingTheory.PowerSeries.P2fac_eq_sum]
      unfold Commons.RingTheory.PowerSeries.P2sum Commons.RingTheory.PowerSeries.P1fac
        Commons.RingTheory.PowerSeries.P0fac
      simp only [add_mul, sub_mul, Commons.RingTheory.PowerSeries.coeff_add_s,
        Commons.RingTheory.PowerSeries.coeff_sub_s]
      rw [show (-X * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))) : PowerSeries ℚ) = C (-1 : ℚ) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))) by simp,
        show (X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))) by simp,
        show ((-1 : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) (Yvu a b))) = C (-1 : ℚ) * X ^ 0 * (PowerSeries.derivative (R := ℚ) (Yvu a b)) by simp,
        show ((3 : PowerSeries ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yvu a b))) = C (3 : ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yvu a b)) by
          rw [← map_ofNat PowerSeries.C 3],
        show (C (8 * a * b) * X * (PowerSeries.derivative (R := ℚ) (Yvu a b))) = C (8 * a * b) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (Yvu a b)) by rw [pow_one],
        show (C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X * (Yvu a b))
          = C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X ^ 1 * (Yvu a b) by rw [pow_one],
        show (C (a * b) * (Yvu a b)) = C (a * b) * X ^ 0 * (Yvu a b) by simp,
        show (X ^ 5 * (Yvu a b) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 5 * (Yvu a b) by simp]
      repeat' rw [coeff_C_pow_deriv2_gen]
      repeat' rw [coeff_C_pow_deriv_gen]
      repeat' rw [coeff_C_pow_mul_gen]
      simp only [Yvu, PowerSeries.coeff_mk]
      norm_num [beukersV_zero, beukersV_one, beukersV_two, beukersV_three, beukersV_eval4,
        beukersV_eval5, beukersV_eval6, beukersV_eval7, beukersV_eval8, beukersU_zero,
        beukersU_one, beukersU_two, beukersU_eval3, beukersU_eval4, beukersU_eval5,
        beukersU_eval6, beukersU_eval7, beukersU_eval8]
      try ring

/-- The coefficients `n ≤ 6` of the operator applied to `mk (f·g)`, for the
pair `uv`. -/
theorem coeff_LHS_uv_small (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b)))
      + Commons.RingTheory.PowerSeries.P1fac a b * (PowerSeries.derivative (R := ℚ) (Yuv a b)) + Commons.RingTheory.PowerSeries.P0fac a b * (Yuv a b))
      = (if n = 0 then -a else if n = 1 then 3 * b else if n = 2 then -(3 * a)
          else if n = 3 then b else if n = 4 then 0 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · rw [Commons.RingTheory.PowerSeries.P2fac_eq_sum]
      unfold Commons.RingTheory.PowerSeries.P2sum Commons.RingTheory.PowerSeries.P1fac
        Commons.RingTheory.PowerSeries.P0fac
      simp only [add_mul, sub_mul, Commons.RingTheory.PowerSeries.coeff_add_s,
        Commons.RingTheory.PowerSeries.coeff_sub_s]
      rw [show (-X * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))) : PowerSeries ℚ) = C (-1 : ℚ) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))) by simp,
        show (X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))) by simp,
        show ((-1 : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) (Yuv a b))) = C (-1 : ℚ) * X ^ 0 * (PowerSeries.derivative (R := ℚ) (Yuv a b)) by simp,
        show ((3 : PowerSeries ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yuv a b))) = C (3 : ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yuv a b)) by
          rw [← map_ofNat PowerSeries.C 3],
        show (C (8 * a * b) * X * (PowerSeries.derivative (R := ℚ) (Yuv a b))) = C (8 * a * b) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (Yuv a b)) by rw [pow_one],
        show (C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X * (Yuv a b))
          = C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X ^ 1 * (Yuv a b) by rw [pow_one],
        show (C (a * b) * (Yuv a b)) = C (a * b) * X ^ 0 * (Yuv a b) by simp,
        show (X ^ 5 * (Yuv a b) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 5 * (Yuv a b) by simp]
      repeat' rw [coeff_C_pow_deriv2_gen]
      repeat' rw [coeff_C_pow_deriv_gen]
      repeat' rw [coeff_C_pow_mul_gen]
      simp only [Yuv, PowerSeries.coeff_mk]
      norm_num [beukersV_zero, beukersV_one, beukersV_two, beukersV_three, beukersV_eval4,
        beukersV_eval5, beukersV_eval6, beukersV_eval7, beukersV_eval8, beukersU_zero,
        beukersU_one, beukersU_two, beukersU_eval3, beukersU_eval4, beukersU_eval5,
        beukersU_eval6, beukersU_eval7, beukersU_eval8]
      try ring

/-- The coefficients `n ≤ 6` of the operator applied to `mk (f·g)`, for the
pair `vv`. -/
theorem coeff_LHS_vv_small (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b)))
      + Commons.RingTheory.PowerSeries.P1fac a b * (PowerSeries.derivative (R := ℚ) (Yvv a b)) + Commons.RingTheory.PowerSeries.P0fac a b * (Yvv a b))
      = (if n = 0 then -1 else if n = 1 then 0 else if n = 2 then 2
          else if n = 3 then 0 else if n = 4 then -1 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · rw [Commons.RingTheory.PowerSeries.P2fac_eq_sum]
      unfold Commons.RingTheory.PowerSeries.P2sum Commons.RingTheory.PowerSeries.P1fac
        Commons.RingTheory.PowerSeries.P0fac
      simp only [add_mul, sub_mul, Commons.RingTheory.PowerSeries.coeff_add_s,
        Commons.RingTheory.PowerSeries.coeff_sub_s]
      rw [show (-X * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))) : PowerSeries ℚ) = C (-1 : ℚ) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))) by simp,
        show (X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))) by simp,
        show ((-1 : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) (Yvv a b))) = C (-1 : ℚ) * X ^ 0 * (PowerSeries.derivative (R := ℚ) (Yvv a b)) by simp,
        show ((3 : PowerSeries ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yvv a b))) = C (3 : ℚ) * X ^ 6 * (PowerSeries.derivative (R := ℚ) (Yvv a b)) by
          rw [← map_ofNat PowerSeries.C 3],
        show (C (8 * a * b) * X * (PowerSeries.derivative (R := ℚ) (Yvv a b))) = C (8 * a * b) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (Yvv a b)) by rw [pow_one],
        show (C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X * (Yvv a b))
          = C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X ^ 1 * (Yvv a b) by rw [pow_one],
        show (C (a * b) * (Yvv a b)) = C (a * b) * X ^ 0 * (Yvv a b) by simp,
        show (X ^ 5 * (Yvv a b) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 5 * (Yvv a b) by simp]
      repeat' rw [coeff_C_pow_deriv2_gen]
      repeat' rw [coeff_C_pow_deriv_gen]
      repeat' rw [coeff_C_pow_mul_gen]
      simp only [Yvv, PowerSeries.coeff_mk]
      norm_num [beukersV_zero, beukersV_one, beukersV_two, beukersV_three, beukersV_eval4,
        beukersV_eval5, beukersV_eval6, beukersV_eval7, beukersV_eval8, beukersU_zero,
        beukersU_one, beukersU_two, beukersU_eval3, beukersU_eval4, beukersU_eval5,
        beukersU_eval6, beukersU_eval7, beukersU_eval8]
      try ring

/-! ## The target polynomials of the three M-identities -/

/-- the coefficient sequence `uₙ(a)·uₙ(b)` of `A(a) ⋆ A(b)` -/
def Yuu (a b : ℚ) : PowerSeries ℚ := PowerSeries.mk (fun m => beukersU a m * beukersU b m)

/-- The right-hand side `−b + 3aX − 3bX² + aX³` of the first M-identity. -/
def RaFam (a b : ℚ) : PowerSeries ℚ :=
  C (-b) * X ^ 0 + C (3 * a) * X ^ 1 + C (-(3 * b)) * X ^ 2 + C a * X ^ 3

/-- The right-hand side `−a + 3bX − 3aX² + bX³` of the second M-identity. -/
def RbFam (a b : ℚ) : PowerSeries ℚ :=
  C (-a) * X ^ 0 + C (3 * b) * X ^ 1 + C (-(3 * a)) * X ^ 2 + C b * X ^ 3

/-- The right-hand side `−1 + 2X² − X⁴` of the third M-identity. -/
def RabFam (a b : ℚ) : PowerSeries ℚ :=
  C (-1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 2 + C (-1 : ℚ) * X ^ 4

lemma coeff_RaFam_le6 (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (RaFam a b) = (if n = 0 then -b else if n = 1 then 3 * a
      else if n = 2 then -(3 * b) else if n = 3 then a
      else if n = 4 then 0 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · simp only [RaFam, Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
      norm_num
      try ring

lemma coeff_RaFam_ge5 (a b : ℚ) (n : ℕ) (hn : 5 ≤ n) :
    PowerSeries.coeff n (RaFam a b) = 0 := by
  rw [RaFam]
  simp only [Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring

lemma coeff_RbFam_le6 (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (RbFam a b) = (if n = 0 then -a else if n = 1 then 3 * b
      else if n = 2 then -(3 * a) else if n = 3 then b
      else if n = 4 then 0 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · simp only [RbFam, Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
      norm_num
      try ring

lemma coeff_RbFam_ge5 (a b : ℚ) (n : ℕ) (hn : 5 ≤ n) :
    PowerSeries.coeff n (RbFam a b) = 0 := by
  rw [RbFam]
  simp only [Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring

lemma coeff_RabFam_le6 (a b : ℚ) (n : ℕ) (hn : n ≤ 6) :
    PowerSeries.coeff n (RabFam a b) = (if n = 0 then -1 else if n = 1 then 0
      else if n = 2 then 2 else if n = 3 then 0
      else if n = 4 then -1 else if n = 5 then 0 else if n = 6 then 0 else 0) := by
  interval_cases n <;>
    · simp only [RabFam, Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
      norm_num
      try ring

lemma coeff_RabFam_ge5 (a b : ℚ) (n : ℕ) (hn : 5 ≤ n) :
    PowerSeries.coeff n (RabFam a b) = 0 := by
  rw [RabFam]
  simp only [Commons.RingTheory.PowerSeries.coeff_add_s, PowerSeries.coeff_C_mul_X_pow]
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  ring

/-! ## The certificates for `n ≥ 7` -/

lemma coeff_LHS_vu_big (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yvu a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yvu a b) = 0 := by
  have h := Commons.RingTheory.PowerSeries.coeff_LHS_general a b (RecProp_beukersV a)
    (RecProp_beukersU b) n hn
  simpa [Yvu] using h

lemma coeff_LHS_uv_big (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yuv a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yuv a b) = 0 := by
  have h := Commons.RingTheory.PowerSeries.coeff_LHS_general a b (RecProp_beukersU a)
    (RecProp_beukersV b) n hn
  simpa [Yuv] using h

lemma coeff_LHS_vv_big (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    PowerSeries.coeff n (Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yvv a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yvv a b) = 0 := by
  have h := Commons.RingTheory.PowerSeries.coeff_LHS_general a b (RecProp_beukersV a)
    (RecProp_beukersV b) n hn
  simpa [Yvv] using h

/-! ## The three M-identities -/

/-- `M(A(a) ⋆ A(b)) = 0` (the paper's eq. (ODE), restated in the operator normal form). -/
theorem logM_uu_commons (a b : ℚ) :
    Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuu a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yuu a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yuu a b = 0 := by
  have hY : Yuu a b = PA a b := by
    ext n
    simp [Yuu, PA, hadamard_coeff, beukersA_coeff, PowerSeries.coeff_mk]
  rw [hY]
  have h := logPA_ode a b
  simpa [Commons.RingTheory.PowerSeries.P2fac, Commons.RingTheory.PowerSeries.P1fac,
    Commons.RingTheory.PowerSeries.P0fac, logPAODE, logPAP2, logPAP1, logPAP0, logPAQ4,
    Commons.RingTheory.PowerSeries.Q4fac] using h

theorem logM_vu_commons (a b : ℚ) :
    Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvu a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yvu a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yvu a b = RaFam a b := by
  ext n
  by_cases hn : n ≤ 6
  · rw [coeff_LHS_vu_small a b n hn, coeff_RaFam_le6 a b n hn]
  · rw [coeff_LHS_vu_big a b n (by omega), coeff_RaFam_ge5 a b n (by omega)]

theorem logM_uv_commons (a b : ℚ) :
    Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yuv a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yuv a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yuv a b = RbFam a b := by
  ext n
  by_cases hn : n ≤ 6
  · rw [coeff_LHS_uv_small a b n hn, coeff_RbFam_le6 a b n hn]
  · rw [coeff_LHS_uv_big a b n (by omega), coeff_RbFam_ge5 a b n (by omega)]

theorem logM_vv_commons (a b : ℚ) :
    Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yvv a b))
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) (Yvv a b)
      + Commons.RingTheory.PowerSeries.P0fac a b * Yvv a b = RabFam a b := by
  ext n
  by_cases hn : n ≤ 6
  · rw [coeff_LHS_vv_small a b n hn, coeff_RabFam_le6 a b n hn]
  · rw [coeff_LHS_vv_big a b n (by omega), coeff_RabFam_ge5 a b n (by omega)]

/-! ## Linearity of the operator, and the inhomogeneous ODE for `logP` -/

lemma logPAODE_add (a b : ℚ) (Y Z : PowerSeries ℚ) :
    logPAODE a b (Y + Z) = logPAODE a b Y + logPAODE a b Z := by
  unfold logPAODE
  simp only [map_add]
  ring

lemma logPAODE_sub (a b : ℚ) (Y Z : PowerSeries ℚ) :
    logPAODE a b (Y - Z) = logPAODE a b Y - logPAODE a b Z := by
  unfold logPAODE
  simp only [map_sub]
  ring

lemma logPAODE_C_mul (a b : ℚ) (c : ℚ) (Y : PowerSeries ℚ) :
    logPAODE a b (PowerSeries.C c * Y) = PowerSeries.C c * logPAODE a b Y := by
  have h1 : ∀ Z : PowerSeries ℚ, (PowerSeries.derivative (R := ℚ)) (PowerSeries.C c * Z)
      = PowerSeries.C c * (PowerSeries.derivative (R := ℚ)) Z := by
    intro Z
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul]
  unfold logPAODE
  simp only [h1]
  ring

/-! ## The operator in the certificate's normal form -/

/-- The operator in the normal form of the commons certificate. -/
lemma logPAODE_eq_commons (a b : ℚ) (Y : PowerSeries ℚ) :
    logPAODE a b Y = Commons.RingTheory.PowerSeries.P2fac a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y)
      + Commons.RingTheory.PowerSeries.P1fac a b * PowerSeries.derivative (R := ℚ) Y
      + Commons.RingTheory.PowerSeries.P0fac a b * Y := by
  unfold logPAODE logPAP2 logPAP1 logPAP0
  simp only [Commons.RingTheory.PowerSeries.P2fac, Commons.RingTheory.PowerSeries.P1fac,
    Commons.RingTheory.PowerSeries.P0fac, Commons.RingTheory.PowerSeries.Q4fac, logPAQ4]

/-- `M(A(a) ⋆ A(b)) = 0` (paper eq. (ODE)). -/
theorem logM_uu (a b : ℚ) : logPAODE a b (Yuu a b) = 0 := by
  rw [logPAODE_eq_commons a b (Yuu a b)]
  exact logM_uu_commons a b

/-- **First M-identity** (paper §"The overconvergent space"):
`M(H(a) ⋆ A(b)) = −b + 3aX − 3bX² + aX³`. -/
theorem logM_vu (a b : ℚ) : logPAODE a b (Yvu a b) = RaFam a b := by
  rw [logPAODE_eq_commons a b (Yvu a b)]
  exact logM_vu_commons a b

/-- **Second M-identity**: `M(A(a) ⋆ H(b)) = −a + 3bX − 3aX² + bX³`. -/
theorem logM_uv (a b : ℚ) : logPAODE a b (Yuv a b) = RbFam a b := by
  rw [logPAODE_eq_commons a b (Yuv a b)]
  exact logM_uv_commons a b

/-- **Third M-identity**: `M(H(a) ⋆ H(b)) = −1 + 2X² − X⁴`. -/
theorem logM_vv (a b : ℚ) : logPAODE a b (Yvv a b) = RabFam a b := by
  rw [logPAODE_eq_commons a b (Yvv a b)]
  exact logM_vv_commons a b

/-- **The unlikely `G`-function satisfies an inhomogeneous ODE with polynomial
right-hand side.**  Under the relation (rabc) — which is exactly the statement
that the coefficients of `logP` are those of `r_a·P_a + r_b·P_b + r_ab·P_ab`
(`LogUnlikelyG.logPCoeff_eq_rat`) — the rational series `logP` satisfies
`M(logP) = r_a(−b + 3aX − 3bX² + aX³) + r_b(−a + 3bX − 3aX² + bX³)
+ r_ab(−1 + 2X² − X⁴)`, a polynomial with rational coefficients. -/
theorem logP_ode (ã₁ ã₂ : ℚ) (ra rb rab r0 : ℤ) :
    logPAODE ã₁ ã₂ (logP ã₁ ã₂ ra rb rab r0)
      = PowerSeries.C (ra : ℚ) * RaFam ã₁ ã₂ + PowerSeries.C (rb : ℚ) * RbFam ã₁ ã₂
        + PowerSeries.C (rab : ℚ) * RabFam ã₁ ã₂ := by
  have hdecomp : logP ã₁ ã₂ ra rb rab r0
      = PowerSeries.C (ra : ℚ) * Yvu ã₁ ã₂ + PowerSeries.C (rb : ℚ) * Yuv ã₁ ã₂
        + PowerSeries.C (rab : ℚ) * Yvv ã₁ ã₂ - PowerSeries.C (r0 : ℚ) * Yuu ã₁ ã₂ := by
    ext n
    simp only [logP, logPCoeffQ, Yvu, Yuv, Yvv, Yuu, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul, Commons.RingTheory.PowerSeries.coeff_add_s,
      Commons.RingTheory.PowerSeries.coeff_sub_s]
    try ring
  rw [hdecomp, logPAODE_sub, logPAODE_add, logPAODE_add, logPAODE_C_mul, logPAODE_C_mul,
    logPAODE_C_mul, logPAODE_C_mul, logM_vu, logM_uv, logM_vv, logM_uu]
  try ring

end

end Submission.CDT
