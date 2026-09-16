import Mathlib.RingTheory.PowerSeries.Basic

open PowerSeries

namespace Commons.RingTheory.PowerSeries

/-- The coefficient of `p * X` in a power series (the `n = 1` case of `coeff_mul_X_pow'`). -/
lemma coeff_mul_X {R : Type*} [Semiring R] (p : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (p * PowerSeries.X) = if 1 ≤ n then PowerSeries.coeff (n - 1) p else 0 := by
  simpa using PowerSeries.coeff_mul_X_pow' (R := R) p 1 n

end Commons.RingTheory.PowerSeries
