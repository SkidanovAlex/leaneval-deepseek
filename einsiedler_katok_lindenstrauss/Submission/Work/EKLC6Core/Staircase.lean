import Mathlib
import Submission.Work.Misiurewicz.frontier_finite_subset

/-!
# The `staircase` decomposition of a finite family of sets

Given a finite family `U : Fin m → Set X`, the *staircase* piece of index `j` is

`staircase U j = U j \ ⋃ {U k | k < j}`,

i.e. the part of `U j` that is not already covered by the preceding members of the family.
The pieces are pairwise disjoint, their union is `⋃ j, U j`, and each piece is contained in
`U j`; when the `U j` are measurable (resp. have controllable frontier) the same holds for the
pieces.  Together with the complement of `⋃ j, U j` they form the finite partition used in
`exists_staircase_partition`.
-/

namespace Work.EKLC6Core

open Set

/-- The `j`-th staircase piece of the family `U`: `U j` with all earlier `U k` (`k < j`)
removed. -/
def staircase {X : Type*} {m : ℕ} (U : Fin m → Set X) (j : Fin m) : Set X :=
  U j \ ⋃ k : {k : Fin m // k.val < j.val}, U k.val

/-- Each staircase piece is contained in the corresponding member of the family. -/
theorem staircase_subset {X : Type*} {m : ℕ} (U : Fin m → Set X) (j : Fin m) :
    staircase U j ⊆ U j :=
  Set.sdiff_subset

/-- Staircase pieces of measurable sets are measurable. -/
theorem staircase_measurable {X : Type*} {m : ℕ} [MeasurableSpace X] {U : Fin m → Set X}
    (hU : ∀ j, MeasurableSet (U j)) (j : Fin m) : MeasurableSet (staircase U j) := by
  refine MeasurableSet.diff (hU j) ?_
  exact MeasurableSet.iUnion fun k => hU k.val

/-- The frontier of a set difference is contained in the union of the frontiers. -/
theorem frontier_sdiff_subset {X : Type*} [TopologicalSpace X] (s t : Set X) :
    frontier (s \ t) ⊆ frontier s ∪ frontier t := by
  simpa [Set.sdiff_eq] using Work.Misiurewicz.frontier_inter_subset_union s tᶜ

end Work.EKLC6Core
