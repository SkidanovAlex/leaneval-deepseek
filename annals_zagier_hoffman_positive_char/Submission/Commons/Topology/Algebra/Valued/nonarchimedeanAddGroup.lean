import Mathlib.Topology.Algebra.Valued.ValuedField

namespace Commons.Topology.Algebra.Valued

/-- The additive group of a valued field, equipped with the uniform space and topology
induced by its valuation, is nonarchimedean: every neighbourhood of zero contains an
open additive subgroup. -/
theorem nonarchimedeanAddGroup {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀] :
    letI : UniformSpace K := vK.toUniformSpace
    letI : TopologicalSpace K := UniformSpace.toTopologicalSpace
    NonarchimedeanAddGroup K := by
  constructor
  intro U hU
  rcases (Valued.mem_nhds_zero.mp hU) with ⟨γ, hγ⟩
  let H : AddSubgroup K := (vK.v.restrict).ltAddSubgroup γ
  refine ⟨{ toAddSubgroup := H, isOpen' := ?_ }, ?_⟩
  · change IsOpen {x : K | vK.v.restrict x < γ.1}
    exact Valued.isOpen_ball K γ.1
  · intro x hx
    change x ∈ H at hx
    apply hγ
    exact (Valuation.mem_ltAddSubgroup_iff.mp hx)

end Commons.Topology.Algebra.Valued