import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.PowerSeries


/-- The ascending factorial `(k + 1).ascFactorial j`, viewed in a field of
characteristic zero, is nonzero. -/
lemma cast_ascFactorial_ne_zero {K : Type*} [Field K] [CharZero K] (k j : ℕ) :
    (((k + 1).ascFactorial j : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact (Nat.ascFactorial_pos k j).ne'

/-- The `k`-th coefficient of the `j`-fold formal derivative vanishes if and only
if the `(k + j)`-th coefficient of `f` vanishes, over a field of characteristic
zero. -/
lemma coeff_iterate_derivative_eq_zero_iff {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (j k : ℕ) :
    PowerSeries.coeff k ((PowerSeries.derivative (R := K))^[j] f) = 0 ↔
      PowerSeries.coeff (k + j) f = 0 := by
  rw [PowerSeries.coeff_iterate_derivative]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (cast_ascFactorial_ne_zero k j)
    · exact h2
  · intro h
    rw [h, mul_zero]

/-- If `f : K⟦X⟧` has order exactly `N` and `j ≤ N`, then the `j`-fold formal
derivative `f^[j]` has order exactly `N - j`. -/
theorem order_iterate_derivative {K : Type*} [Field K] [CharZero K] (f : PowerSeries K) (j N : ℕ)
    (hN : PowerSeries.order f = (N : ℕ∞)) (hj : j ≤ N) :
    PowerSeries.order ((PowerSeries.derivative (R := K))^[j] f) = ((N - j : ℕ) : ℕ∞) := by
  obtain ⟨hNne, hNzero⟩ := (PowerSeries.order_eq_nat (φ := f) (n := N)).mp hN
  rw [PowerSeries.order_eq_nat]
  constructor
  · intro hzero
    rw [coeff_iterate_derivative_eq_zero_iff, Nat.sub_add_cancel hj] at hzero
    exact hNne hzero
  · intro i hi
    rw [coeff_iterate_derivative_eq_zero_iff]
    exact hNzero (i + j) (by omega)

end Commons.RingTheory.PowerSeries