import Mathlib

namespace Work.EKLRelProduct

open MeasureTheory

/-- If `S` carries all of the mass of `μ` (its complement is null) and `μ S ≠ ⊤`,
then every set has finite `μ`-measure. -/
theorem measure_ne_top_of_compl_eq_zero {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {S : Set α} (hcar : μ Sᶜ = 0) (htop : μ S ≠ ⊤) (t : Set α) : μ t ≠ ⊤ := by
  have hle : μ t ≤ μ S := by
    calc μ t = μ ((t ∩ S) ∪ (t ∩ Sᶜ)) := by
          congr 1
          ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
          tauto
      _ ≤ μ (t ∩ S) + μ (t ∩ Sᶜ) := measure_union_le _ _
      _ ≤ μ S + μ Sᶜ :=
            add_le_add (measure_mono Set.inter_subset_right) (measure_mono Set.inter_subset_right)
      _ = μ S := by rw [hcar, add_zero]
  intro ht
  exact htop (eq_top_iff.mpr (ht ▸ hle))

end Work.EKLRelProduct
