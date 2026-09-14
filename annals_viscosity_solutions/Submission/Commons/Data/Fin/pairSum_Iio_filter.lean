import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

lemma pairSum_Iio_filter {N : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin N → Fin N → α) :
    (∑ j : Fin N, (∑ i ∈ Finset.Iio j, f i j)) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), f p.1 p.2 := by
  calc
    (∑ j : Fin N, (∑ i ∈ Finset.Iio j, f i j))
        = ∑ j : Fin N, ∑ i : Fin N, if i < j then f i j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          have hIio : Finset.Iio j = Finset.univ.filter (fun i : Fin N => i < j) := by
            ext i
            simp
          rw [hIio, Finset.sum_filter]
    _ = (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), f p.1 p.2) := by
          rw [Finset.sum_filter]
          rw [Fintype.sum_prod_type]
          symm
          rw [Finset.sum_comm]

end Commons.Data.Fin