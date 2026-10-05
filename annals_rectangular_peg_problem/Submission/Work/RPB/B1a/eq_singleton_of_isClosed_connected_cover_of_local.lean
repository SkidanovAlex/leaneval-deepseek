import Mathlib

namespace Work.RPB.B1a

/-- If a preconnected set `C` contains a point `p`, and `U` is an open neighbourhood of `p`
such that `C ∩ U ⊆ {p}`, then `C = {p}`.

Indeed, `C ⊆ {p} ∪ Uᶜ`; if `C` contained a point `b ≠ p` then `C` would meet both closed
sets `{p}` and `Uᶜ`, so by preconnectedness it would meet their (empty) intersection. -/
lemma eq_singleton_of_preconnected_of_inter_subset_singleton {α : Type*} [TopologicalSpace α]
    [T1Space α] (C U : Set α) (p : α) (hCpre : IsPreconnected C) (hpC : p ∈ C)
    (hUop : IsOpen U) (hpU : p ∈ U) (hCU : C ∩ U ⊆ {p}) : C = {p} := by
  have hcover : C ⊆ ({p} : Set α) ∪ Uᶜ := by
    intro x hxC
    by_cases hxU : x ∈ U
    · exact Or.inl (hCU ⟨hxC, hxU⟩)
    · exact Or.inr (by simpa using hxU)
  have hsub : C ⊆ {p} := by
    by_contra h
    obtain ⟨b, hbC, hbnotp⟩ := Set.not_subset.mp h
    have hbU : b ∉ U := fun hbU => hbnotp (hCU ⟨hbC, hbU⟩)
    have hcontra := isPreconnected_closed_iff.1 hCpre {p} Uᶜ isClosed_singleton
      hUop.isClosed_compl hcover ⟨p, hpC, rfl⟩ ⟨b, hbC, by simpa using hbU⟩
    obtain ⟨x, -, hxp, hxu⟩ := hcontra
    rw [Set.mem_singleton_iff] at hxp
    exact hxu (hxp ▸ hpU)
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨hpC, fun x hx => by have := hsub hx; rwa [Set.mem_singleton_iff] at this⟩

theorem eq_singleton_of_isClosed_connected_cover_of_local (A B S U W : Set ℂ) (p : ℂ)
    (hAcl : IsClosed A) (hBcl : IsClosed B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hUop : IsOpen U) (hpU : p ∈ U) (hpA : p ∈ A) (hpB : p ∈ B)
    (hAB : A ∪ B = S) (hint : A ∩ B ⊆ {p})
    (hWpc : IsPreconnected W) (hWsub : W ⊆ S ∩ U) (hWnotp : p ∉ W) (hclW : S ∩ U ⊆ closure W) :
    A = {p} ∨ B = {p} := by
  have hWAB : W ⊆ A ∪ B := fun x hx => by
    rw [hAB]; exact (hWsub hx).1
  -- `W` is preconnected and disjoint from `A ∩ B ⊆ {p}`, so `W ⊆ A` or `W ⊆ B`.
  have hWsplit : W ⊆ A ∨ W ⊆ B := by
    by_cases hWA : (W ∩ A).Nonempty
    · by_cases hWB : (W ∩ B).Nonempty
      · exfalso
        have hcontra := isPreconnected_closed_iff.1 hWpc A B hAcl hBcl hWAB hWA hWB
        obtain ⟨x, hxW, hxAB⟩ := hcontra
        have hxp : x ∈ ({p} : Set ℂ) := hint hxAB
        rw [Set.mem_singleton_iff] at hxp
        exact hWnotp (hxp ▸ hxW)
      · left
        intro x hxW
        rcases hWAB hxW with h | h
        · exact h
        · exact absurd ⟨x, hxW, h⟩ hWB
    · right
      intro x hxW
      rcases hWAB hxW with h | h
      · exact absurd ⟨x, hxW, h⟩ hWA
      · exact h
  rcases hWsplit with hWA | hWB
  · -- `W ⊆ A` gives `closure W ⊆ A`, hence `S ∩ U ⊆ A` and `B ∩ U ⊆ A ∩ B ⊆ {p}`.
    right
    have hclA : closure W ⊆ A := hAcl.closure_subset_iff.mpr hWA
    have hSUA : S ∩ U ⊆ A := fun x hx => hclA (hclW hx)
    have hBU : B ∩ U ⊆ {p} := by
      intro x hx
      have hxS : x ∈ S := by rw [← hAB]; exact Or.inr hx.1
      exact hint ⟨hSUA ⟨hxS, hx.2⟩, hx.1⟩
    exact eq_singleton_of_preconnected_of_inter_subset_singleton B U p hBc.isPreconnected
      hpB hUop hpU hBU
  · -- `W ⊆ B` gives `closure W ⊆ B`, hence `S ∩ U ⊆ B` and `A ∩ U ⊆ A ∩ B ⊆ {p}`.
    left
    have hclB : closure W ⊆ B := hBcl.closure_subset_iff.mpr hWB
    have hSUB : S ∩ U ⊆ B := fun x hx => hclB (hclW hx)
    have hAU : A ∩ U ⊆ {p} := by
      intro x hx
      have hxS : x ∈ S := by rw [← hAB]; exact Or.inl hx.1
      exact hint ⟨hx.1, hSUB ⟨hxS, hx.2⟩⟩
    exact eq_singleton_of_preconnected_of_inter_subset_singleton A U p hAc.isPreconnected
      hpA hUop hpU hAU

end Work.RPB.B1a
