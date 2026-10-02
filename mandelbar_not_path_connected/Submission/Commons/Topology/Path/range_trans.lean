import Mathlib.Topology.Path

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Path

theorem range_trans {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z) : Set.range (γ.trans γ') = Set.range γ ∪ Set.range γ' := by
  exact Path.trans_range γ γ'

end Commons.Topology.Path