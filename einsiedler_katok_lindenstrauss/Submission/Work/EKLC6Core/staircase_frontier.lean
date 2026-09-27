import Mathlib
import Submission.Work.EKLC6Core.Staircase

namespace Work.EKLC6Core

open Set

theorem staircase_frontier {X : Type*} {m : ℕ} [TopologicalSpace X] (U : Fin m → Set X)
    (j : Fin m) :
    frontier (Work.EKLC6Core.staircase U j) ⊆ ⋃ k, frontier (U k) := by
  intro x hx
  have hsdiff : x ∈ frontier (U j \ ⋃ k : {k : Fin m // k.val < j.val}, U k.val) := by
    simpa only [staircase] using hx
  have h1 := frontier_sdiff_subset (U j) (⋃ k : {k : Fin m // k.val < j.val}, U k.val) hsdiff
  rcases h1 with h | h
  · exact mem_iUnion.mpr ⟨j, h⟩
  · have h2 := Work.Misiurewicz.frontier_iUnion_subset
      (fun k : {k : Fin m // k.val < j.val} => U k.val) h
    rcases mem_iUnion.mp h2 with ⟨k, hk⟩
    exact mem_iUnion.mpr ⟨k.val, hk⟩

end Work.EKLC6Core
