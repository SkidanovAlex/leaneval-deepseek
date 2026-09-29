import Mathlib.RingTheory.PowerSeries.Derivative

open scoped BigOperators

namespace Commons.RingTheory.PowerSeries

lemma iterate_derivative_coeff (R : Type*) [CommSemiring R] (f : PowerSeries R) (i k : ℕ) :
    PowerSeries.coeff k ((fun g : PowerSeries R => (PowerSeries.derivative (R := R)) g)^[i] f) =
      (∏ t ∈ Finset.range i, (((k + t : ℕ) : R) + 1)) * PowerSeries.coeff (k + i) f := by
  rw [PowerSeries.coeff_iterate_derivative]
  congr 1
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro t ht
  push_cast
  ring

end Commons.RingTheory.PowerSeries