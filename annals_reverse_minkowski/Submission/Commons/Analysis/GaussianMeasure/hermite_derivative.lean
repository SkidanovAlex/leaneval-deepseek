import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.Hermite.Basic

open Polynomial

namespace Commons.Analysis.GaussianMeasure

/-- The formal derivative of the `n`-th probabilists' Hermite polynomial:
`d/dx He_n = n · He_{n-1}`. -/
theorem hermite_derivative_poly (m : ℕ) :
    Polynomial.derivative (Polynomial.hermite m) =
      Polynomial.C (m : ℤ) * Polynomial.hermite (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Polynomial.hermite_succ]
    rw [Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_C_mul]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hcast : Polynomial.C ((m + 1 + 1 : ℕ) : ℤ) =
          Polynomial.C ((m + 1 : ℕ) : ℤ) + 1 := by
        rw [show ((m + 1 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring]
        rw [map_add, map_one]
      rw [hcast, Polynomial.hermite_succ m]
      ring

theorem hermite_derivative (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => Polynomial.aeval y (Polynomial.hermite (n + 1))) x
      = ((n + 1 : ℕ) : ℝ) * Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.deriv_aeval]
  rw [hermite_derivative_poly (n + 1)]
  rw [Nat.add_sub_cancel]
  rw [map_mul, Polynomial.aeval_C]
  simp

end Commons.Analysis.GaussianMeasure
