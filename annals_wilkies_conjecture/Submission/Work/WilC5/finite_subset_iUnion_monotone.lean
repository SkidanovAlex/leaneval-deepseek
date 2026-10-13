import Mathlib

namespace Work.WilC5

theorem finite_subset_iUnion_monotone {M ι : Type} [LinearOrder ι] [Nonempty ι]
    {A : ι → Set M} (hmono : Monotone A) {T : Set M} (hT : T.Finite) (hTA : T ⊆ ⋃ i, A i) :
    ∃ i, T ⊆ A i := by
  classical
  rcases Set.eq_empty_or_nonempty T with hT0 | ⟨x0, hx0⟩
  · exact ⟨Classical.arbitrary ι, by rw [hT0]; exact Set.empty_subset _⟩
  · -- choose, for each `x ∈ T`, an index whose `A`-set contains `x`
    let f : M → ι := fun x =>
      if hx : x ∈ T then Classical.choose (Set.mem_iUnion.mp (hTA hx)) else Classical.arbitrary ι
    have hf : ∀ x (hx : x ∈ T), x ∈ A (f x) := by
      intro x hx
      have h1 : f x = Classical.choose (Set.mem_iUnion.mp (hTA hx)) := dite_eq_left hx
      rw [h1]
      exact Classical.choose_spec (Set.mem_iUnion.mp (hTA hx))
    -- the finite set of chosen indices
    have hSne : (hT.toFinset.image f).Nonempty :=
      ⟨f x0, Finset.mem_image.mpr ⟨x0, (Set.Finite.mem_toFinset hT).mpr hx0, rfl⟩⟩
    refine ⟨(hT.toFinset.image f).max' hSne, ?_⟩
    intro x hx
    have hxmem : x ∈ hT.toFinset := (Set.Finite.mem_toFinset hT).mpr hx
    have hfx : f x ∈ hT.toFinset.image f := Finset.mem_image.mpr ⟨x, hxmem, rfl⟩
    have hle : f x ≤ (hT.toFinset.image f).max' hSne := Finset.le_max' _ _ hfx
    exact hmono hle (hf x hx)

end Work.WilC5
