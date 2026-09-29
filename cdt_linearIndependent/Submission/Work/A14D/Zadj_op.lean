import Mathlib
import Submission.Work.A14D.Zadj_defs

namespace Work.A14D

open Polynomial

/-- Derivative of the cubic `P = X - 10X² + 9X³`. -/
lemma Zadj_op_deriv_P2 : (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ).derivative
    = (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ) := by
  simp only [map_sub, map_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_ofNat]
  simp only [Polynomial.C_eq_natCast]
  ring

/-- Derivative of `P' = 1 - 20X + 27X²`. -/
lemma Zadj_op_deriv_P1 : (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).derivative
    = (-20 + 54 * X : Polynomial ℂ) := by
  simp only [map_sub, map_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_ofNat, Polynomial.derivative_one]
  simp only [Polynomial.C_eq_natCast]
  ring

/-- Two Leibniz steps: `(P·β)'' = P''·β + 2·P'·β' + P·β''`. -/
lemma Zadj_op_second (p : Polynomial ℂ) (β : RatFunc ℂ) :
    Submission.CDT.dRat (Submission.CDT.dRat
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p * β))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative.derivative * β
        + 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative * Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p
            * Submission.CDT.dRat (Submission.CDT.dRat β) := by
  rw [Submission.CDT.dRat_poly_mul]
  rw [Submission.CDT.dRat_add, Submission.CDT.dRat_poly_mul, Submission.CDT.dRat_poly_mul]
  ring

/-- The first-order Leibniz rule for `P' = 1 - 20X + 27X²`. -/
lemma Zadj_op_first (β : RatFunc ℂ) :
    Submission.CDT.dRat
        ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ)) * β)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          ((1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ).derivative) * β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2 : Polynomial ℂ)
            * Submission.CDT.dRat β := by
  rw [Submission.CDT.dRat_poly_mul]

theorem Zadj_op (β : RatFunc ℂ) : LZc β = LZf β := by
  rw [LZc, LZf, Zadj_op_second (X - 10 * X ^ 2 + 9 * X ^ 3 : Polynomial ℂ) β,
    Zadj_op_first β, Zadj_op_deriv_P2, Zadj_op_deriv_P1]
  simp only [P2Z, P1Z, P0Z]
  ring

end Work.A14D
