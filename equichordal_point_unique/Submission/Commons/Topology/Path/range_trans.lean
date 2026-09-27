import Mathlib.Topology.Path

namespace Commons.Topology.Path

theorem range_trans {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z) : Set.range (γ.trans γ') = Set.range γ ∪ Set.range γ' := by
  exact Path.trans_range γ γ'

end Commons.Topology.Path