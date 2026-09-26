import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

theorem exists_rank_of_strict_order {ι : Type} [Fintype ι] (R : ι → ι → Prop)
    (hirr : ∀ i : ι, ¬ R i i) (htrans : ∀ i j k : ι, R i j → R j k → R i k) :
    ∃ rank : ι → ℕ, ∀ i j : ι, R i j → rank j < rank i := by
  classical
  -- Rank an element by the cardinality of the set of elements strictly below it.
  refine ⟨fun i => (Finset.univ.filter (fun k => R i k)).card, ?_⟩
  intro i j hij
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · -- Transitivity: everything below `j` is below `i`.
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact htrans i j k hij hk
  · -- `j` itself lies below `i` but not below `j` (irreflexivity), so strictness.
    intro heq
    have h1 : j ∈ Finset.univ.filter (fun k => R j k) := by
      rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact hirr j h1

end Work.Topology.SphereSlicing
