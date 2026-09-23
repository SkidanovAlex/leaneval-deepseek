import Mathlib.Topology.Maps.Proper.Basic

namespace Commons.Topology.ClosedGraph

theorem exists_continuous_selection_of_closed_unique_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (S : Set (X × Y)) (hS : IsClosed S) (h : ∀ x, ∃! y, (x, y) ∈ S) :
    ∃ f : X → Y, Continuous f ∧ ∀ x, (x, f x) ∈ S := by
  classical
  have hf : ∀ x, (x, (h x).choose) ∈ S := fun x => (h x).choose_spec.1
  refine ⟨fun x => (h x).choose, ?_, hf⟩
  rw [continuous_iff_isClosed]
  intro C hC
  have himg : (fun x => (h x).choose) ⁻¹' C = Prod.fst '' (S ∩ (Set.univ ×ˢ C)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, (h x).choose), ⟨hf x, ⟨Set.mem_univ x, hx⟩⟩, rfl⟩
    · rintro ⟨p, hp, hp2⟩
      obtain ⟨hpS, _, hpC⟩ := hp
      obtain ⟨x', y'⟩ := p
      change (h x).choose ∈ C
      have hx : x' = x := hp2
      have hy : y' = (h x').choose := (h x').choose_spec.2 y' hpS
      rw [← hx, ← hy]
      exact hpC
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ (hS.inter (isClosed_univ.prod hC))

end Commons.Topology.ClosedGraph