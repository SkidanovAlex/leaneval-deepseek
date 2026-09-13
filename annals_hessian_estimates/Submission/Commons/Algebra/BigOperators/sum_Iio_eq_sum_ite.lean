import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Algebra.BigOperators

theorem sum_Iio_eq_sum_ite {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M)
    (j : Fin n) :
    (∑ i ∈ Finset.Iio j, f i) = ∑ i : Fin n, (if i < j then f i else 0) := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [Finset.mem_Iio]

end Commons.Algebra.BigOperators