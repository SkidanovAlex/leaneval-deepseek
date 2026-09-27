import Mathlib

/-!
# The frontier of a finite union / intersection

For a finite family of sets `f : ι → Set X` (`ι` finite),

* `frontier (⋂ i, f i) ⊆ ⋃ i, frontier (f i)`,
* `frontier (⋃ i, f i) ⊆ ⋃ i, frontier (f i)`.

Consequently any finite union of null-frontier sets again has null frontier, which is what the
"staircase"/"join" construction of a null-frontier finite partition needs.
-/

namespace Work.Misiurewicz

section

open Set

variable {X ι : Type*} [TopologicalSpace X]

theorem frontier_inter_subset_union (s t : Set X) :
    frontier (s ∩ t) ⊆ frontier s ∪ frontier t := by
  intro x hx
  rcases frontier_inter_subset s t hx with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

theorem frontier_union_subset_union (s t : Set X) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  intro x hx
  have hx' : x ∈ closure (s ∪ t) ∩ closure (s ∪ t)ᶜ := by
    rwa [frontier_eq_closure_inter_closure] at hx
  obtain ⟨hcl, hclc⟩ := hx'
  rw [closure_union, mem_union] at hcl
  rcases hcl with hs | ht
  · left
    rw [frontier_eq_closure_inter_closure, mem_inter_iff]
    exact ⟨hs, closure_mono (compl_subset_compl.mpr subset_union_left) hclc⟩
  · right
    rw [frontier_eq_closure_inter_closure, mem_inter_iff]
    exact ⟨ht, closure_mono (compl_subset_compl.mpr subset_union_right) hclc⟩

theorem frontier_biInter_subset (s : Finset ι) (f : ι → Set X) :
    frontier (⋂ i ∈ s, f i) ⊆ ⋃ i ∈ s, frontier (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert, Finset.set_biUnion_insert]
    exact (frontier_inter_subset_union (f a) (⋂ i ∈ s, f i)).trans
      (Set.union_subset_union subset_rfl ih)

theorem frontier_biUnion_subset (s : Finset ι) (f : ι → Set X) :
    frontier (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ s, frontier (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
    exact (frontier_union_subset_union (f a) (⋃ i ∈ s, f i)).trans
      (Set.union_subset_union subset_rfl ih)

theorem frontier_iInter_subset [Fintype ι] (f : ι → Set X) :
    frontier (⋂ i, f i) ⊆ ⋃ i, frontier (f i) := by
  simpa using frontier_biInter_subset (Finset.univ : Finset ι) f

theorem frontier_iUnion_subset [Fintype ι] (f : ι → Set X) :
    frontier (⋃ i, f i) ⊆ ⋃ i, frontier (f i) := by
  simpa using frontier_biUnion_subset (Finset.univ : Finset ι) f

end

end Work.Misiurewicz
