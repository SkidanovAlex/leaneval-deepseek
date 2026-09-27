import Mathlib

namespace Work.Embedding

/-- A closed subset of a compact space, every point of which has an open neighbourhood meeting the
subset only in that point ("all points isolated"), is finite.  (The closedness hypothesis cannot be
dropped: `{1/n : n ≥ 1} ⊆ [0,1]` satisfies the isolation condition but is infinite.) -/
theorem finite_of_isClosed_forall_isolated {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {D : Set X} (hD : IsClosed D)
    (hiso : ∀ p ∈ D, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ∩ D ⊆ {p}) : D.Finite := by
  classical
  choose W hWo hWp hWD using hiso
  have hcomp : IsCompact D := hD.isCompact
  have hcover : D ⊆ ⋃ p : D, W p.1 p.2 := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hWp x hx⟩
  obtain ⟨t, ht⟩ :=
    hcomp.elim_finite_subcover (fun p : D => W p.1 p.2) (fun p => hWo p.1 p.2) hcover
  refine Set.Finite.subset (Finset.finite_toSet (t.image (fun p : D => p.1))) ?_
  intro x hx
  obtain ⟨p, hpt, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
  have hmem : x ∈ W p.1 p.2 ∩ D := ⟨hxp, hx⟩
  have hsingle := hWD p.1 p.2 hmem
  simp only [Set.mem_singleton_iff] at hsingle
  rw [hsingle]
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, hpt, rfl⟩)

end Work.Embedding
