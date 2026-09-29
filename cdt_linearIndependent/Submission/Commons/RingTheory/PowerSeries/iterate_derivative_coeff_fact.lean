import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The coefficient of the `i`-th iterate of `PowerSeries.derivative`

The `k`-th coefficient of the `i`-fold formal derivative of `f : PowerSeries ℚ`
is `(k + i)! / k!` times the `(k + i)`-th coefficient of `f`.
-/

namespace Commons.RingTheory.PowerSeries

lemma iterate_derivative_coeff_fact (f : PowerSeries ℚ) (i k : ℕ) :
    PowerSeries.coeff k ((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[i] f) =
      ((Nat.factorial (k + i) : ℚ) / (Nat.factorial k : ℚ)) * PowerSeries.coeff (k + i) f := by
  have hk0 : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
  have hfact : ((k + 1).ascFactorial i : ℚ) =
      (Nat.factorial (k + i) : ℚ) / (Nat.factorial k : ℚ) := by
    field_simp [hk0]
    rw [mul_comm]
    exact_mod_cast (Nat.factorial_mul_ascFactorial k i)
  rw [PowerSeries.coeff_iterate_derivative, hfact]

end Commons.RingTheory.PowerSeries
