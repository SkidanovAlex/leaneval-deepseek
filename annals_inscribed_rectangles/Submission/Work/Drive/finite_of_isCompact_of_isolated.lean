import Mathlib

namespace Work.Drive

/-- A compact set in which every point is isolated (has an open neighbourhood meeting
the set only in that point) is finite: the induced topology on `s` is discrete, and a
compact discrete space is finite. -/
theorem finite_of_isCompact_of_isolated {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsCompact s) (h : ∀ x ∈ s, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ∩ s ⊆ {x}) :
    s.Finite := by
  classical
  set f : s → Set α := fun x => Classical.choose (h x.1 x.2)
  have hf_open : ∀ x : s, IsOpen (f x) := fun x => (Classical.choose_spec (h x.1 x.2)).1
  have hf_mem : ∀ x : s, x.1 ∈ f x := fun x => (Classical.choose_spec (h x.1 x.2)).2.1
  have hf_sub : ∀ x : s, f x ∩ s ⊆ {x.1} := fun x => (Classical.choose_spec (h x.1 x.2)).2.2
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover f hf_open
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hf_mem ⟨y, hy⟩⟩)
  refine (t.finite_toSet.image Subtype.val).subset ?_
  intro y hy
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
  exact (Set.mem_image Subtype.val ↑t y).mpr ⟨i, hi, by simpa using (hf_sub i ⟨hyi, hy⟩).symm⟩

end Work.Drive
