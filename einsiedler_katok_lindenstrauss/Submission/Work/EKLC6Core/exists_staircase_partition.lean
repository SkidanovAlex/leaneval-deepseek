import Mathlib
import Submission.Work.Misiurewicz.frontier_finite_subset
import Submission.Work.EKLC6Core.Staircase
import Submission.Work.EKLC6Core.staircase_iUnion
import Submission.Work.EKLC6Core.staircase_disjoint
import Submission.Work.EKLC6Core.staircase_frontier

namespace Work.EKLC6Core

open Set

/-- The *staircase partition* induced by a finite family `U : Fin m → Set X`: at index
`Fin.castSucc j` it is the staircase piece `staircase U j` (the part of `U j` not already
covered by the earlier members), and the extra last index carries the complement of the
whole union `⋃ j, U j`. -/
def staircasePart {X : Type*} {m : ℕ} (U : Fin m → Set X) : Fin (m + 1) → Set X :=
  Fin.snoc (staircase U) (⋃ j, U j)ᶜ

/-- The last piece of the staircase partition is the complement of the union. -/
theorem staircasePart_last {X : Type*} {m : ℕ} (U : Fin m → Set X) :
    staircasePart U (Fin.last m) = (⋃ j, U j)ᶜ := by
  rw [staircasePart, Fin.snoc_last]

/-- The `j`-th piece of the staircase partition is `staircase U j`. -/
theorem staircasePart_castSucc {X : Type*} {m : ℕ} (U : Fin m → Set X) (j : Fin m) :
    staircasePart U (Fin.castSucc j) = staircase U j := by
  rw [staircasePart, Fin.snoc_castSucc]

/-- An index of `Fin (m+1)` different from the last one is of the form `Fin.castSucc j`; in
particular its value is `< m`. -/
theorem val_lt_of_ne_last {m : ℕ} {i : Fin (m + 1)} (hi : i ≠ Fin.last m) : i.val < m := by
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
  · exact h
  · exact absurd (Fin.ext h) hi

theorem exists_staircase_partition {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {m : ℕ}
    (U : Fin m → Set X) (hUmeas : ∀ i, MeasurableSet (U i)) :
    ∃ (P : Fin (m + 1) → Set X) (i₀ : Fin (m + 1)),
      (∀ i, i ≠ i₀ → ∃ j, P i ⊆ U j) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = Set.univ ∧
      P i₀ = (⋃ j, U j)ᶜ ∧
      (∀ i, MeasurableSet (P i)) ∧
      (∀ i, frontier (P i) ⊆ ⋃ j, frontier (U j)) := by
  classical
  refine ⟨staircasePart U, Fin.last m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every piece other than the last one is contained in a member of the family.
    intro i hi
    have hlt : i.val < m := val_lt_of_ne_last hi
    obtain ⟨j, hj⟩ : ∃ j : Fin m, i = Fin.castSucc j := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    refine ⟨j, ?_⟩
    have hval : staircasePart U i = staircase U j := by rw [hj, staircasePart_castSucc]
    rw [hval]
    exact staircase_subset U j
  · -- The pieces are pairwise disjoint.
    intro i j hij
    by_cases hi : i = Fin.last m
    · rw [hi, staircasePart_last]
      have hj : j ≠ Fin.last m := fun h => hij (hi.trans h.symm)
      have hlt : j.val < m := val_lt_of_ne_last hj
      have hsub : staircasePart U j ⊆ ⋃ k, U k := by
        obtain ⟨j', hj'⟩ : ∃ j' : Fin m, j = Fin.castSucc j' := ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
        have hv : staircasePart U j = staircase U j' := by rw [hj', staircasePart_castSucc]
        rw [hv]
        exact (staircase_subset U _).trans (Set.subset_iUnion U _)
      exact Set.disjoint_left.mpr (fun a ha hb => ha (hsub hb))
    · by_cases hj : j = Fin.last m
      · rw [hj, staircasePart_last]
        have hi' : i ≠ Fin.last m := fun h => hij (h.trans hj.symm)
        have hlt : i.val < m := val_lt_of_ne_last hi'
        have hsub : staircasePart U i ⊆ ⋃ k, U k := by
          obtain ⟨i', hi'⟩ : ∃ i' : Fin m, i = Fin.castSucc i' := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
          have hv : staircasePart U i = staircase U i' := by rw [hi', staircasePart_castSucc]
          rw [hv]
          exact (staircase_subset U _).trans (Set.subset_iUnion U _)
        exact Set.disjoint_right.mpr (fun a ha hb => ha (hsub hb))
      · obtain ⟨i', hi'⟩ : ∃ i' : Fin m, i = Fin.castSucc i' :=
          ⟨⟨i.val, val_lt_of_ne_last hi⟩, Fin.ext rfl⟩
        obtain ⟨j', hj'⟩ : ∃ j' : Fin m, j = Fin.castSucc j' :=
          ⟨⟨j.val, val_lt_of_ne_last hj⟩, Fin.ext rfl⟩
        have h1 : staircasePart U i = staircase U i' := by rw [hi', staircasePart_castSucc]
        have h2 : staircasePart U j = staircase U j' := by rw [hj', staircasePart_castSucc]
        rw [h1, h2]
        refine staircase_disjoint U (fun h => hij ?_)
        rw [hi', hj', h]
  · -- The pieces cover the whole space.
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ ⋃ j : Fin m, U j
    · have hx' : x ∈ ⋃ j : Fin m, staircase U j := by rwa [staircase_iUnion]
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
      exact Set.mem_iUnion.mpr ⟨Fin.castSucc j, by rwa [staircasePart_castSucc]⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.last m, by rwa [staircasePart_last]⟩
  · -- The distinguished piece is the complement of the union.
    exact staircasePart_last U
  · -- All pieces are measurable.
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi, staircasePart_last]
      exact MeasurableSet.compl (MeasurableSet.iUnion hUmeas)
    · have hlt : i.val < m := val_lt_of_ne_last hi
      obtain ⟨i', hi'⟩ : ∃ i' : Fin m, i = Fin.castSucc i' := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
      have hv : staircasePart U i = staircase U i' := by rw [hi', staircasePart_castSucc]
      rw [hv]
      exact staircase_measurable hUmeas _
  · -- The frontier of every piece is contained in the union of the frontiers.
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi, staircasePart_last, frontier_compl]
      exact Work.Misiurewicz.frontier_iUnion_subset U
    · have hlt : i.val < m := val_lt_of_ne_last hi
      obtain ⟨i', hi'⟩ : ∃ i' : Fin m, i = Fin.castSucc i' := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
      have hv : staircasePart U i = staircase U i' := by rw [hi', staircasePart_castSucc]
      rw [hv]
      exact staircase_frontier U _

end Work.EKLC6Core
