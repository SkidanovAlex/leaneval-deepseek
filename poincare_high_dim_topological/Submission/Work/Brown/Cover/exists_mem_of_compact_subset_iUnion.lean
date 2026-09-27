import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cover

/-- If a compact set is covered by a monotone increasing sequence of open sets,
then it is already contained in one of them. -/
theorem exists_mem_of_compact_subset_iUnion {X : Type*} [TopologicalSpace X] {U : ℕ → Set X} (hopen : ∀ k, IsOpen (U k)) (hmono : Monotone U) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ ⋃ k, U k) : ∃ k, K ⊆ U k := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hopen hKU
  refine ⟨t.sup id, fun x hx => ?_⟩
  have hx' : x ∈ ⋃ i ∈ t, U i := ht hx
  simp only [Set.mem_iUnion] at hx'
  obtain ⟨i, hi, hxi⟩ := hx'
  exact hmono (Finset.le_sup (f := id) hi) hxi

end Work.Brown.Cover
