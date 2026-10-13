import Mathlib.Topology.MetricSpace.Holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The `dist`/`HolderWith` bridge.**  A pointwise bound of the form
`dist (f x) (f y) ≤ C * (dist x y) ^ r` with real exponent upgrades to `HolderWith C r f`
(which is stated with `edist` and the `ennreal` power). -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : NNReal} {f : X → Y} (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_nndist, edist_nndist]
  rw [← ENNReal.coe_rpow_of_nonneg (nndist x y) r.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist]
  exact h x y

end Work.Stability
