import Mathlib
import Submission.Work.EKLC6Core.Staircase

namespace Work.EKLC6Core

open Set

/-- Two staircase pieces of distinct indices are disjoint: if `i < j` then
`staircase U i ⊆ U i ⊆ ⋃_{k<j} U k` is excluded from `staircase U j`, and
symmetrically when `j < i`. -/
theorem staircase_disjoint {X : Type*} {m : ℕ} (U : Fin m → Set X) {i j : Fin m} (h : i ≠ j) :
    Disjoint (Work.EKLC6Core.staircase U i) (Work.EKLC6Core.staircase U j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [staircase, Set.mem_sdiff] at hxi hxj
  obtain ⟨hxiU, hxni⟩ := hxi
  obtain ⟨hxjU, hxnj⟩ := hxj
  rcases lt_or_gt_of_ne h with hij | hji
  · exact hxnj (Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hxiU⟩)
  · exact hxni (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxjU⟩)

end Work.EKLC6Core
