import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

lemma sum_Iio_add_Ioi_eq_erase {N : ℕ} {α : Type*} [AddCommMonoid α] (k : Fin N) (f : Fin N → α) :
    (∑ i ∈ Finset.Iio k, f i) + (∑ i ∈ Finset.Ioi k, f i) = ∑ i ∈ Finset.univ.erase k, f i := by
  have hdisj : Disjoint (Finset.Iio k) (Finset.Ioi k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp at ha hb
    exact (lt_asymm hb) ha
  have hset : Finset.Iio k ∪ Finset.Ioi k = Finset.univ.erase k := by
    ext i
    simp
  rw [← Finset.sum_union hdisj]
  rw [hset]

end Commons.Data.Fin