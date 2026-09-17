import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finite.Prod

namespace Commons.Data.List

/-- There are only finitely many lists of a fixed length over a finite alphabet. -/
theorem finite_setOf_length_eq {α : Type*} [Fintype α] (N : ℕ) :
    {l : List α | l.length = N}.Finite := by
  have hsub : {l : List α | l.length = N} ⊆
      List.ofFn '' (Set.univ : Set (Fin N → α)) := by
    intro l hl
    refine ⟨fun i : Fin N => l.get (Fin.cast hl.symm i), Set.mem_univ _, ?_⟩
    exact (List.ofFn_congr hl l.get).symm.trans (List.ofFn_get l)
  exact (Set.finite_univ.image (List.ofFn : (Fin N → α) → List α)).subset hsub

/-- There are only finitely many words over a finite alphabet with prescribed letter
multiplicities. -/
theorem finite_setOf_count_eq {α : Type*} [Fintype α] [DecidableEq α] (n : α → ℕ) :
    {l : List α | ∀ i, l.count i = n i}.Finite := by
  refine (finite_setOf_length_eq (∑ i, n i)).subset ?_
  intro l hl
  show l.length = ∑ i, n i
  rw [← List.sum_toFinset_count_eq_length l]
  rw [Finset.sum_congr rfl (fun a _ => hl a)]
  refine Finset.sum_subset (Finset.subset_univ l.toFinset) ?_
  intro x _ hx
  have hx' : x ∉ l := by simpa using hx
  rw [← hl x, List.count_eq_zero_of_not_mem hx']

end Commons.Data.List