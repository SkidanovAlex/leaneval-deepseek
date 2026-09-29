import Mathlib.Data.ENat.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

namespace Commons.RingTheory.PowerSeries

/-- If in a finite family of power series over a field one term has strictly
smaller order than all the others, then the order of the whole sum is the order
of that term. -/
theorem order_finset_sum_eq_of_forall_lt {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (g : ι → PowerSeries K) (i : ι) (hi : i ∈ s)
    (hmin : ∀ j ∈ s, j ≠ i → PowerSeries.order (g i) < PowerSeries.order (g j)) :
    PowerSeries.order (∑ j ∈ s, g j) = PowerSeries.order (g i) := by
  refine le_antisymm ?_ ?_
  · -- The sum has order at most that of the distinguished term: its
    -- coefficient at index `(order (g i)).toNat` is that of `g i`.
    by_cases htop : PowerSeries.order (g i) = ⊤
    · rw [htop]; exact le_top
    · have hf : g i ≠ 0 := PowerSeries.order_eq_top.not.mp htop
      have hcoe : (↑(PowerSeries.order (g i)).toNat : ℕ∞) = PowerSeries.order (g i) :=
        PowerSeries.coe_toNat_order hf
      have hsum : (∑ j ∈ s, (PowerSeries.coeff (PowerSeries.order (g i)).toNat) (g j))
          = (PowerSeries.coeff (PowerSeries.order (g i)).toNat) (g i) :=
        Finset.sum_eq_single_of_mem i hi fun j hj hji =>
          PowerSeries.coeff_of_lt_order _ (by rw [hcoe]; exact hmin j hj hji)
      have hne : (PowerSeries.coeff (PowerSeries.order (g i)).toNat) (∑ j ∈ s, g j) ≠ 0 := by
        rw [map_sum, hsum]
        exact PowerSeries.coeff_order hf
      have hle := PowerSeries.order_le (PowerSeries.order (g i)).toNat hne
      simpa [hcoe] using hle
  · -- The sum has order at least that of the distinguished term, since every
    -- coefficient below `order (g i)` vanishes termwise.
    refine PowerSeries.le_order (∑ j ∈ s, g j) (PowerSeries.order (g i)) fun m hm => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact PowerSeries.coeff_of_lt_order m hm
    · exact PowerSeries.coeff_of_lt_order m (lt_trans hm (hmin j hj hji))

end Commons.RingTheory.PowerSeries