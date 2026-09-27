import Mathlib

namespace Work.EKLComp

open MeasureTheory Set

/-- If `ν` is a finite measure and each `c i` (measurable, over a countable index type)
has full measure `ν Set.univ`, then so does the countable intersection `⋂ i, c i`. -/
theorem measure_iInter_eq_of_forall_eq_univ {α : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {ι : Type*} [Countable ι] {c : ι → Set α}
    (hmeas : ∀ i, MeasurableSet (c i)) (hfin : ν Set.univ ≠ ⊤)
    (h : ∀ i, ν (c i) = ν Set.univ) : ν (⋂ i, c i) = ν Set.univ := by
  -- Each complement `(c i)ᶜ` is null, since `ν (c i) = ν univ` is finite.
  have hnull : ∀ i, ν ((c i)ᶜ) = 0 := by
    intro i
    have hci : ν (c i) ≠ ⊤ := by rw [h i]; exact hfin
    rw [measure_compl (hmeas i) hci]
    simp [h i]
  -- `univ \ ⋂ i, c i = ⋃ i, (c i)ᶜ` is a countable union of null sets, hence null.
  refine measure_eq_measure_of_null_sdiff (subset_univ _) ?_
  have hset : Set.univ \ ⋂ i, c i = ⋃ i, (c i)ᶜ := by
    rw [← Set.compl_eq_univ_sdiff, Set.compl_iInter]
  rw [hset]
  exact measure_iUnion_null hnull

end Work.EKLComp
