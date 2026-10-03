import Mathlib.Topology.Path

namespace Commons.Topology.Path

theorem range_symm {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) : Set.range γ.symm = Set.range γ := by
  exact Path.symm_range γ

end Commons.Topology.Path