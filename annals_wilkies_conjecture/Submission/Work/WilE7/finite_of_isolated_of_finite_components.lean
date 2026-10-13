import Mathlib

namespace Work.WilE7

/-- If every point of `F` is isolated in the subspace `F` (i.e. for each `x ∈ F` there is an
open `U` with `U ∩ F = {x}`), then `F` is totally disconnected: every preconnected subset of
`F` is a subsingleton.

Key point: for `a ∈ F`, the set `F \ {a}` is relatively open in `F`, witnessed by
`W := ⋃_{y ∈ F, y ≠ a} U_y` where `U_y` isolates `y`. -/
theorem isTotallyDisconnected_of_isolated {α : Type*} [TopologicalSpace α] {F : Set α}
    (hiso : ∀ x ∈ F, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ∩ F = {x}) :
    IsTotallyDisconnected F := by
  intro t htF htpre a ha b hb
  by_contra hne
  obtain ⟨U, hUo, haU, hUF⟩ := hiso a (htF ha)
  -- `W` is the union of isolating neighbourhoods of all points of `F` other than `a`.
  let W : Set α := ⋃ y : α, ⋃ (_h : y ∈ F ∧ y ≠ a), (hiso y _h.1).choose
  have hWeq : W = ⋃ y : α, ⋃ (_h : y ∈ F ∧ y ≠ a), (hiso y _h.1).choose := rfl
  have hWo : IsOpen W := by
    rw [hWeq]
    exact isOpen_iUnion fun y => isOpen_iUnion fun h => (hiso y h.1).choose_spec.1
  have hWF : W ∩ F = F \ {a} := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨hzW, hzF⟩ := hz
      rw [hWeq, Set.mem_iUnion] at hzW
      obtain ⟨y, hzy⟩ := hzW
      rw [Set.mem_iUnion] at hzy
      obtain ⟨hy, hzy⟩ := hzy
      have hmem : z ∈ (hiso y hy.1).choose ∩ F := ⟨hzy, hzF⟩
      rw [(hiso y hy.1).choose_spec.2.2] at hmem
      simp only [Set.mem_singleton_iff] at hmem
      refine ⟨hzF, ?_⟩
      intro hza
      exact hy.2 (hmem.symm.trans hza)
    · intro z hz
      obtain ⟨hzF, hza⟩ := hz
      refine ⟨?_, hzF⟩
      rw [hWeq]
      exact Set.mem_iUnion.2
        ⟨z, Set.mem_iUnion.2 ⟨⟨hzF, hza⟩, (hiso z hzF).choose_spec.2.1⟩⟩
  have hdisj : U ∩ W ∩ F = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨⟨hzu, hzW⟩, hzF⟩ := hz
    have hza : z = a := by
      have h1 : z ∈ U ∩ F := ⟨hzu, hzF⟩
      rw [hUF] at h1
      simpa using h1
    have h2 : z ∈ F \ {a} := by
      have h2' : z ∈ W ∩ F := ⟨hzW, hzF⟩
      rwa [hWF] at h2'
    exact h2.2 (by simpa using hza)
  have ht_sub : t ⊆ U ∪ W := by
    intro z hz
    have hzF : z ∈ F := htF hz
    by_cases hza : z = a
    · exact Or.inl (by rw [hza]; exact haU)
    · refine Or.inr ?_
      have hzW : z ∈ W ∩ F := by rw [hWF]; exact ⟨hzF, hza⟩
      exact hzW.1
  have hnu : (t ∩ U).Nonempty := ⟨a, ha, haU⟩
  have hnv : (t ∩ W).Nonempty := by
    refine ⟨b, hb, ?_⟩
    rw [hWeq]
    exact Set.mem_iUnion.2
      ⟨b, Set.mem_iUnion.2 ⟨⟨htF hb, fun h => hne h.symm⟩, (hiso b (htF hb)).choose_spec.2.1⟩⟩
  obtain ⟨z, hzt, hzu, hzW⟩ := htpre U W hUo hWo ht_sub hnu hnv
  have hzmem : z ∈ U ∩ W ∩ F := ⟨⟨hzu, hzW⟩, htF hzt⟩
  rw [hdisj] at hzmem
  exact hzmem

theorem finite_of_isolated_of_finite_components {α : Type*} [TopologicalSpace α] {F : Set α}
    (hiso : ∀ x ∈ F, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ∩ F = {x})
    {s : Finset α} (hs : (↑s : Set α) ⊆ F)
    (hcomp : ∀ x ∈ F, ∃ y ∈ s, connectedComponentIn F x = connectedComponentIn F y) :
    Set.Finite F := by
  have hTD : IsTotallyDisconnected F := isTotallyDisconnected_of_isolated hiso
  have hsub : F ⊆ (↑s : Set α) := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hcomp x hx
    have hxmem : x ∈ connectedComponentIn F y := heq ▸ mem_connectedComponentIn hx
    have hysub : (connectedComponentIn F y).Subsingleton :=
      hTD _ (connectedComponentIn_subset F y) isPreconnected_connectedComponentIn
    have hxy : x = y := hysub hxmem (mem_connectedComponentIn (hs (Finset.mem_coe.mpr hy)))
    exact Finset.mem_coe.mpr (hxy.symm ▸ hy)
  exact s.finite_toSet.subset hsub

end Work.WilE7
