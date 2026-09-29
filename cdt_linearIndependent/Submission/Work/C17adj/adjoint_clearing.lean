import Mathlib
import Submission.Work.C17.adjoint_defs

/-!
# Clearing denominators in the adjoint certificate

This file proves `Work.C17adj.adjoint_clearing`: if `β = N/D` (with `D = X^6(X-1)^2(X+1)^2`)
satisfies the inhomogeneous second order equation
`(P₂β)'' - (P₁β)' + P₀β = Σᵢ cᵢ y^{i-4} dy`
in `ℚ(x)`, then the cleared polynomial identity `Epoly a b n c = 0` holds.

The proof is a pure computation with the derivation `dRat` on `RatFunc ℚ`:
multiplying the equation by `D³` and using the quotient rule turns it into the
explicit polynomial identity `Epoly a b n c = 0`.
-/

namespace Work.C17adj

open Polynomial

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

noncomputable section

/-! ## Clearing the denominators of `Σᵢ cᵢ y^{i-4} dy` -/

theorem gD3_clearing (i : Fin 6) :
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj) ^ 3
        * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.gD3 i) := by
  have hx : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hx1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by
    intro h
    have h2 : (RatFunc.X : RatFunc ℚ) = 1 := sub_eq_zero.mp h
    rw [← RatFunc.algebraMap_X, ← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ))] at h2
    have h3 : (Polynomial.X : Polynomial ℚ) = 1 :=
      IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) h2
    have h4 : (Polynomial.X - 1 : Polynomial ℚ) ≠ 0 := by
      intro hh
      have hc := congrArg (fun p : Polynomial ℚ => p.eval 0) hh
      norm_num at hc
    exact h4 (sub_eq_zero.mpr h3)
  have hyQ : Work.C17.yQ ≠ 0 := by
    rw [Work.C17.yQ, Work.C17.xQ]
    exact div_ne_zero (pow_ne_zero 2 hx) hx1
  rw [zpow_sub₀ hyQ, zpow_natCast]
  fin_cases i <;>
    (simp only [Work.C17.gD3]
     simp
     simp only [Work.C17.Dadj, Work.C17.yQ, Work.C17.xQ, Work.C17.dyQ,
       Work.C17.gD3_0, Work.C17.gD3_1, Work.C17.gD3_2, Work.C17.gD3_3, Work.C17.gD3_4,
       Work.C17.gD3_5, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
       map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat, map_one,
       Nat.cast_ofNat, mul_one, one_mul]
     field_simp
     ring)

/-! ## Derivative bookkeeping for the concrete polynomials -/

theorem Npoly_derivative (n : Fin 7 → ℚ) :
    (Work.C17.Npoly n).derivative = Work.C17.NpolyD n := by
  rw [Work.C17.Npoly, Work.C17.NpolyD]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (n k) ((k : ℕ) : ℚ)]

theorem NpolyD_derivative (n : Fin 7 → ℚ) :
    (Work.C17.NpolyD n).derivative = Work.C17.NpolyDD n := by
  rw [Work.C17.NpolyD, Work.C17.NpolyDD]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k _
  fin_cases k <;> norm_num <;> (simp only [← C_mul]; congr 1; ring)

theorem Dadj_derivative : (Work.C17.Dadj).derivative = Work.C17.Dadj1 := by
  simp only [Work.C17.Dadj, Work.C17.Dadj1, derivative_add, derivative_C_mul_X_pow]
  norm_num

theorem Dadj1_derivative : (Work.C17.Dadj1).derivative = Work.C17.Dadj2 := by
  simp only [Work.C17.Dadj1, Work.C17.Dadj2, derivative_add, derivative_C_mul_X_pow]
  norm_num

theorem Dadj_ne_zero : (Work.C17.Dadj : Polynomial ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 10) h
  simp only [Work.C17.Dadj, coeff_add, coeff_C_mul_X_pow, coeff_zero] at hc
  norm_num at hc

theorem Badj_eq_deriv (a b : ℚ) :
    Work.C17.Badj a b = 2 * (Work.C17.P2x a b).derivative - Work.C17.P1x a b := by
  simp only [Work.C17.Badj, Work.C17.P1x, Work.C17.P2x, Work.C17.Q4x, derivative_add, derivative_mul,
    derivative_sub, derivative_X, derivative_C, derivative_one, derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one, map_zero,
    Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add, add_zero,
    pow_one]
  ring

theorem Cadj_eq_deriv (a b : ℚ) :
    Work.C17.Cadj a b
      = (Work.C17.P2x a b).derivative.derivative - (Work.C17.P1x a b).derivative + Work.C17.P0x a b := by
  simp only [Work.C17.Cadj, Work.C17.P1x, Work.C17.P2x, Work.C17.P0x, Work.C17.Q4x, derivative_add,
    derivative_mul, derivative_sub, derivative_neg, derivative_X, derivative_C, derivative_one,
    derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one, map_zero,
    Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add, add_zero,
    pow_one]
  ring

/-! ## The general denominator-clearing identity -/

/-- Clearing the denominators `d³` from `(p₂·n/d)'' - (p₁·n/d)' + p₀·n/d`. -/
theorem dRat_clearing_general {K : Type*} [Field K] (p2 p1 p0 nn d : Polynomial K) (hd : d ≠ 0) :
    (algebraMap (Polynomial K) (RatFunc K) d)^3 *
      (Submission.CDT.dRat (Submission.CDT.dRat (algebraMap (Polynomial K) (RatFunc K) p2 *
              (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d)))
       - Submission.CDT.dRat (algebraMap (Polynomial K) (RatFunc K) p1 *
              (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d))
       + algebraMap (Polynomial K) (RatFunc K) p0 *
              (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d))
    = algebraMap (Polynomial K) (RatFunc K)
        (p2 * (nn.derivative.derivative * d^2 - nn * d * d.derivative.derivative
              - 2 * nn.derivative * d * d.derivative + 2 * nn * d.derivative^2)
         + (2 * p2.derivative - p1) * (d * (nn.derivative * d - nn * d.derivative))
         + (p2.derivative.derivative - p1.derivative + p0) * (d^2 * nn)) := by
  have hd' : (algebraMap (Polynomial K) (RatFunc K) d) ≠ 0 := fun h =>
    hd (IsFractionRing.injective (Polynomial K) (RatFunc K) (by rw [h, map_zero]))
  have e1 : Submission.CDT.dRat (algebraMap (Polynomial K) (RatFunc K) p2 *
      (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d))
      = algebraMap (Polynomial K) (RatFunc K) ((p2 * nn).derivative * d - (p2 * nn) * d.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 2 := by
    rw [← mul_div_assoc, ← map_mul, Submission.CDT.dRat_div]
  have e2 : Submission.CDT.dRat (algebraMap (Polynomial K) (RatFunc K)
        ((p2 * nn).derivative * d - (p2 * nn) * d.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 2)
      = algebraMap (Polynomial K) (RatFunc K)
          (((p2 * nn).derivative * d - (p2 * nn) * d.derivative).derivative * d^2
            - ((p2 * nn).derivative * d - (p2 * nn) * d.derivative) * (d^2).derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 4 := by
    rw [← map_pow, Submission.CDT.dRat_div]
    rw [show (algebraMap (Polynomial K) (RatFunc K) (d ^ 2)) ^ 2
        = (algebraMap (Polynomial K) (RatFunc K) d) ^ 4 by rw [map_pow]; ring]
  have e3 : Submission.CDT.dRat (algebraMap (Polynomial K) (RatFunc K) p1 *
      (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d))
      = algebraMap (Polynomial K) (RatFunc K) ((p1 * nn).derivative * d - (p1 * nn) * d.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 2 := by
    rw [← mul_div_assoc, ← map_mul, Submission.CDT.dRat_div]
  have e4 : algebraMap (Polynomial K) (RatFunc K) p0 *
      (algebraMap (Polynomial K) (RatFunc K) nn / algebraMap (Polynomial K) (RatFunc K) d)
      = algebraMap (Polynomial K) (RatFunc K) (p0 * nn) / algebraMap (Polynomial K) (RatFunc K) d := by
    rw [← mul_div_assoc, ← map_mul]
  set U := ((p2 * nn).derivative * d - (p2 * nn) * d.derivative).derivative * d^2
      - ((p2 * nn).derivative * d - (p2 * nn) * d.derivative) * (d^2).derivative with hU
  set V := (p1 * nn).derivative * d - (p1 * nn) * d.derivative with hV
  set W := U - d^2 * V + d^3 * (p0 * nn) with hW
  have hkey : W = d *
      (p2 * (nn.derivative.derivative * d^2 - nn * d * d.derivative.derivative
              - 2 * nn.derivative * d * d.derivative + 2 * nn * d.derivative^2)
         + (2 * p2.derivative - p1) * (d * (nn.derivative * d - nn * d.derivative))
         + (p2.derivative.derivative - p1.derivative + p0) * (d^2 * nn)) := by
    rw [hW, hU, hV]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add,
      Polynomial.derivative_pow, Nat.cast_ofNat, map_ofNat]
    ring
  rw [e1, e2, e3, e4]
  have hfin : (algebraMap (Polynomial K) (RatFunc K) d)^3 *
      ((algebraMap (Polynomial K) (RatFunc K)) U / (algebraMap (Polynomial K) (RatFunc K) d)^4
       - (algebraMap (Polynomial K) (RatFunc K)) V / (algebraMap (Polynomial K) (RatFunc K) d)^2
       + (algebraMap (Polynomial K) (RatFunc K)) (p0*nn) / (algebraMap (Polynomial K) (RatFunc K)) d)
      = (algebraMap (Polynomial K) (RatFunc K)) W / (algebraMap (Polynomial K) (RatFunc K)) d := by
    rw [hW]
    simp only [map_sub, map_add, map_mul, map_pow]
    field_simp
  rw [hfin, hkey, map_mul]
  exact mul_div_cancel_left₀ _ hd'

/-! ## The two polynomial halves of `Epoly` -/

/-- The `D³`-multiple of `(P₂β)'' - (P₁β)' + P₀β` for `β = N/D`. -/
def LeftPoly (a b : ℚ) (n : Fin 7 → ℚ) : Polynomial ℚ :=
  Work.C17.P2x a b * (Work.C17.NpolyDD n * Work.C17.Dadj ^ 2
        - Work.C17.Npoly n * Work.C17.Dadj * Work.C17.Dadj2
        - 2 * Work.C17.NpolyD n * Work.C17.Dadj * Work.C17.Dadj1
        + 2 * Work.C17.Npoly n * Work.C17.Dadj1 ^ 2)
    + Work.C17.Badj a b * (Work.C17.Dadj * (Work.C17.NpolyD n * Work.C17.Dadj
        - Work.C17.Npoly n * Work.C17.Dadj1))
    + Work.C17.Cadj a b * (Work.C17.Dadj ^ 2 * Work.C17.Npoly n)

/-- The `D³`-multiple of `Σᵢ cᵢ y^{i-4} dy`. -/
def RightPoly (c : Fin 6 → ℚ) : Polynomial ℚ :=
  ∑ i : Fin 6, C (c i) * Work.C17.gD3 i

theorem Epoly_eq (a b : ℚ) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ) :
    Work.C17.Epoly a b n c = LeftPoly a b n - RightPoly c := rfl

/-- The image of a rational number in `ℚ(x)` is the image of the constant polynomial. -/
theorem coe_eq_algebraMap_C (q : ℚ) :
    (q : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C q) := by
  simp


/-! ## The main clearing statement -/

/-- **Adjoint certificate, denominator clearing.**  If `β = N/D` with `D = X^6(X-1)^2(X+1)^2`
solves the inhomogeneous equation `(P₂β)'' - (P₁β)' + P₀β = Σᵢ cᵢ y^{i-4} dy` in `ℚ(x)`,
then the cleared polynomial identity `Epoly a b n c = 0` holds. -/
theorem adjoint_clearing (a b : ℚ) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ) (β : RatFunc ℚ)
    (hβ : β = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.P2Q a b * β))
        - Submission.CDT.dRat (Work.C17.P1Q a b * β) + Work.C17.P0Q a b * β
      = ∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) :
    Work.C17.Epoly a b n c = 0 := by
  have hA : (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
        (Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.P2Q a b * β))
          - Submission.CDT.dRat (Work.C17.P1Q a b * β) + Work.C17.P0Q a b * β)
      = (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
        (∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) := by
    rw [h]
  rw [hβ] at hA
  -- clearing the left hand side
  have hL : (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
      (Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.P2Q a b *
            (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n)
              / algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)))
       - Submission.CDT.dRat (Work.C17.P1Q a b *
            (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n)
              / algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj))
       + Work.C17.P0Q a b *
            (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n)
              / algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj))
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (LeftPoly a b n) := by
    simp only [Work.C17.P2Q, Work.C17.P1Q, Work.C17.P0Q]
    rw [dRat_clearing_general (Work.C17.P2x a b) (Work.C17.P1x a b) (Work.C17.P0x a b)
      (Work.C17.Npoly n) Work.C17.Dadj Dadj_ne_zero]
    apply congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ))
    rw [← Badj_eq_deriv a b, ← Cadj_eq_deriv a b, Npoly_derivative, NpolyD_derivative,
      Dadj_derivative, Dadj1_derivative]
    simp only [LeftPoly]
  -- clearing the right hand side
  have hR : (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
      (∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (RightPoly c) := by
    have per_i : ∀ i : Fin 6, (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3
        * (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.gD3 i) := by
      intro i
      rw [← mul_assoc]
      exact gD3_clearing i
    rw [RightPoly, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
          ((c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C (c i))) *
          ((algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)^3 *
            (Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ)) by
      rw [coe_eq_algebraMap_C]; ring]
    rw [per_i i, ← map_mul]
  have key : algebraMap (Polynomial ℚ) (RatFunc ℚ) (LeftPoly a b n)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (RightPoly c) := by
    rw [← hL, ← hR, hA]
  have hzero : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Epoly a b n c) = 0 := by
    rw [Epoly_eq a b n c, map_sub, key, sub_self]
  exact IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by rw [hzero, map_zero])

end

end Work.C17adj
