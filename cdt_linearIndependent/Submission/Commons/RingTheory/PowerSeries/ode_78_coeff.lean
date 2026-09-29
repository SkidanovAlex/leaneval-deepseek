import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.PowerSeries.Derivative

namespace Commons.RingTheory.PowerSeries


/-- Coefficient of `X * p` at `d`, expressed with natural-number subtraction. -/
lemma coeff_X_mul_ite (p : PowerSeries ℚ) (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.X * p) = if 1 ≤ d then PowerSeries.coeff (d - 1) p else 0 := by
  have h : (PowerSeries.X : PowerSeries ℚ) * p = PowerSeries.X ^ 1 * p := by rw [pow_one]
  rw [h, PowerSeries.coeff_X_pow_mul']

theorem ode_78_coeff (G : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) G)
        + (1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2) * PowerSeries.derivative (R := ℚ) G
        + (-2 - 8 * PowerSeries.X) * G)
      = ((n + 1 : ℕ) : ℚ) ^ 2 * PowerSeries.coeff (n + 1) G
        - (7 * (n : ℚ) ^ 2 + 7 * (n : ℚ) + 2) * PowerSeries.coeff n G
        - 8 * (n : ℚ) ^ 2 * PowerSeries.coeff (n - 1) G := by
  have hE : PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) G)
        + (1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2) * PowerSeries.derivative (R := ℚ) G
        + (-2 - 8 * PowerSeries.X) * G
      = PowerSeries.X * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) G)
        - (PowerSeries.X^2 * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) G)) * 7
        - (PowerSeries.X^3 * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) G)) * 8
        + PowerSeries.derivative (R := ℚ) G
        - (PowerSeries.X * PowerSeries.derivative (R := ℚ) G) * 14
        - (PowerSeries.X^2 * PowerSeries.derivative (R := ℚ) G) * 24
        - G * 2
        - (PowerSeries.X * G) * 8 := by ring
  rw [hE]
  rw [show (7 : PowerSeries ℚ) = PowerSeries.C 7 from rfl,
      show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl,
      show (14 : PowerSeries ℚ) = PowerSeries.C 14 from rfl,
      show (24 : PowerSeries ℚ) = PowerSeries.C 24 from rfl,
      show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl]
  simp only [map_add, map_sub, PowerSeries.coeff_mul_C, coeff_X_mul_ite,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_derivative]
  rcases n with _ | _ | _ | k
  · norm_num
    ring
  · norm_num
    ring
  · norm_num
    ring
  · simp
    ring

end Commons.RingTheory.PowerSeries