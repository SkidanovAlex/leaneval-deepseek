import Mathlib
import Submission.Work.CONDMV.Basic

namespace Work.CONDMV.Refine

/-- In a light profinite set, an open cover by two opens can be refined to a partition into two
clopens. The clopen `B'` is obtained from `exists_clopen_of_closed_subset_open` applied to the
closed set `Aᶜ`, which is contained in the open set `B`; then `A' := B'ᶜ`. -/
theorem exists_isClopen_partition_of_open_cover {S : LightProfinite.{0}} {A B : Set S}
    (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = (Set.univ : Set S)) :
    ∃ A' B' : Set S, IsClopen A' ∧ IsClopen B' ∧ A' ⊆ A ∧ B' ⊆ B ∧
      A' ∪ B' = (Set.univ : Set S) ∧ Disjoint A' B' := by
  -- the complement of `A` is contained in `B`
  have hsub : Aᶜ ⊆ B := by
    intro x hx
    have : x ∈ A ∪ B := by rw [hcov]; trivial
    rcases this with h | h
    · exact absurd h hx
    · exact h
  -- separate the closed set `Aᶜ` from the complement of the open set `B` by a clopen
  obtain ⟨B', hB'cl, hsub₁, hsub₂⟩ :=
    exists_clopen_of_closed_subset_open hA.isClosed_compl hB hsub
  refine ⟨B'ᶜ, B', hB'cl.compl, hB'cl, ?_, hsub₂, ?_, ?_⟩
  · -- `B'ᶜ ⊆ A` because `Aᶜ ⊆ B'`
    intro x hx
    by_contra hxA
    exact hx (hsub₁ hxA)
  · exact Set.compl_union_self B'
  · exact disjoint_compl_left

end Work.CONDMV.Refine
