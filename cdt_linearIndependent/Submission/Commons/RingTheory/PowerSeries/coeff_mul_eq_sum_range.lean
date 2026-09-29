import Mathlib.RingTheory.PowerSeries.Basic

namespace Commons.RingTheory.PowerSeries

lemma coeff_mul_eq_sum_range (R : Type*) [Semiring R] (c f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (c * f) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i c * PowerSeries.coeff (n - i) f := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun p : ℕ × ℕ => PowerSeries.coeff p.1 c * PowerSeries.coeff p.2 f) n

end Commons.RingTheory.PowerSeries