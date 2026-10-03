import Mathlib

namespace Work.Horn.HB

theorem image_connectedComponent_eq_of_isCoveringMap {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [LocallyConnectedSpace E] [LocallyPathConnectedSpace B] {p : E → B}
    (hp : IsCoveringMap p) (e : E) :
    p '' connectedComponent e = connectedComponent (p e) := by
  -- `p '' connectedComponent e` is connected (continuous image of a connected set) and
  -- contains `p e`, so it lies in `connectedComponent (p e)`.
  refine Set.Subset.antisymm (hp.continuous.image_connectedComponent_subset e) ?_
  -- Conversely, `B` is locally path connected, so `connectedComponent (p e) = pathComponent (p e)`;
  -- any point `b` of it is joined to `p e` by a path, and lifting that path through the covering
  -- map starting at `e` exhibits `b` as the image of a point of `connectedComponent e`.
  intro b hb
  rw [← pathComponent_eq_connectedComponent] at hb
  rw [mem_pathComponent_iff] at hb
  obtain ⟨γ⟩ := hb
  refine ⟨(hp.liftPath γ e γ.source) 1, ?_, ?_⟩
  · exact pathComponent_subset_component e (by
      rw [mem_pathComponent_iff]
      exact ⟨⟨hp.liftPath γ e γ.source, hp.liftPath_zero γ e γ.source, rfl⟩⟩)
  · have h := congr_fun (hp.liftPath_lifts γ e γ.source) 1
    simpa [γ.target] using h

end Work.Horn.HB
