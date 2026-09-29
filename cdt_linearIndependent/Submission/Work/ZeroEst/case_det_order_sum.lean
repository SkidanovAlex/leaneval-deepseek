import Mathlib

namespace Work.ZeroEst

/-- For a finite family of power series, if every member has order at least `c`,
then so does the sum. -/
theorem case_det_order_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℚ) (c : ℕ∞)
    (h : ∀ i ∈ s, c ≤ (g i).order) : c ≤ (∑ i ∈ s, g i).order := by
  refine PowerSeries.le_order (∑ i ∈ s, g i) c fun n hn => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun i hi => PowerSeries.coeff_of_lt_order n ?_
  exact lt_of_lt_of_le hn (h i hi)

end Work.ZeroEst
