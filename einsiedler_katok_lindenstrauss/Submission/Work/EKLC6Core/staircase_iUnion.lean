import Mathlib
import Submission.Work.EKLC6Core.Staircase

namespace Work.EKLC6Core

/-- The staircase pieces of a finite family of sets cover exactly the same set as the
family itself. -/
theorem staircase_iUnion {X : Type*} {m : ℕ} (U : Fin m → Set X) :
    (⋃ j : Fin m, Work.EKLC6Core.staircase U j) = ⋃ j, U j := by
  classical
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun j => ?_
    exact Set.Subset.trans (staircase_subset U j) (Set.subset_iUnion U j)
  · intro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨j₀, hj₀⟩ := hx
    set S := Finset.univ.filter (fun j : Fin m => x ∈ U j) with hS
    have hne : S.Nonempty := ⟨j₀, by simp [hS, hj₀]⟩
    obtain ⟨j, hjS, hmin⟩ := Finset.exists_min_image S (fun j : Fin m => j) hne
    have hxj : x ∈ U j := by simpa [hS] using hjS
    refine ⟨j, ?_⟩
    rw [staircase, Set.mem_sdiff]
    refine ⟨hxj, ?_⟩
    intro hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hkS : k.val ∈ S := by simp [hS, hk]
    exact absurd (hmin k.val hkS) (not_le.mpr k.2)

end Work.EKLC6Core
