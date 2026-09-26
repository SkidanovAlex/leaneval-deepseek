import Mathlib.Topology.Homotopy.Basic

namespace Commons.Topology.Homotopy

theorem nullHomotopic_comp_left {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (g : C(Y, Z)) {f : C(X, Y)}
    (hf : ∃ y : Y, ContinuousMap.Homotopic f (ContinuousMap.const X y)) :
    ∃ z : Z, ContinuousMap.Homotopic (g.comp f) (ContinuousMap.const X z) := by
  obtain ⟨y, hy⟩ := hf
  exact ⟨g y, by
    simpa using ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g) hy⟩

end Commons.Topology.Homotopy