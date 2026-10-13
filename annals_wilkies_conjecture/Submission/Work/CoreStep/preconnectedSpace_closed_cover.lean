import Mathlib

namespace Work.CoreStep

theorem preconnectedSpace_closed_cover {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Nonempty X] {ι : Type*} [Finite ι] {U : ι → Set X}
    (hcl : ∀ i, IsClosed (U i))
    (hmeet : ∀ i i', (U i ∩ U i').Nonempty → U i = U i')
    (hcov : (⋃ i, U i) = Set.univ) : ∃ i, U i = Set.univ := by
  -- Pick an index whose set is nonempty (exists because `X` is nonempty and the
  -- sets cover `X`); it suffices to show that this set is all of `X`.
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  rw [Set.mem_iUnion] at hx
  obtain ⟨j, hxj⟩ := hx
  refine ⟨j, ?_⟩
  have hne : (U j).Nonempty := ⟨x, hxj⟩
  -- Two of the `U i` that meet are equal, so `U j` is disjoint from every other
  -- `U i`; hence its complement is a finite union of closed sets, i.e. closed.
  have hclosed_compl : IsClosed ((U j)ᶜ) := by
    have hSfin : ({i | U i ∩ U j = ∅} : Set ι).Finite :=
      Set.finite_univ.subset (Set.subset_univ _)
    have hEq : (U j)ᶜ = ⋃ i ∈ {i | U i ∩ U j = ∅}, U i := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro hy
        have hy' : y ∈ ⋃ i, U i := by rw [hcov]; trivial
        rw [Set.mem_iUnion] at hy'
        obtain ⟨i, hyi⟩ := hy'
        refine ⟨i, ?_, hyi⟩
        by_contra hcon
        have hUi : U i = U j := hmeet i j (Set.nonempty_iff_ne_empty.mpr hcon)
        exact hy (hUi ▸ hyi)
      · rintro ⟨i, hi, hyi⟩ hyj
        have hmem : y ∈ U i ∩ U j := ⟨hyi, hyj⟩
        rw [hi] at hmem
        exact hmem
    rw [hEq]
    exact Set.Finite.isClosed_biUnion hSfin (fun i _ => hcl i)
  -- So `U j` is clopen; in a preconnected space a clopen set is empty or all of `X`.
  have hopen : IsOpen (U j) := isClosed_compl_iff.mp hclosed_compl
  have hclopen : IsClopen (U j) := ⟨hcl j, hopen⟩
  rcases (isClopen_iff.mp hclopen) with h | h
  · exact absurd h hne.ne_empty
  · exact h

end Work.CoreStep
