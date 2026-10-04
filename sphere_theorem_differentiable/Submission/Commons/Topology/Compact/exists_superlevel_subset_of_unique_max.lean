import Mathlib.Analysis.Normed.Order.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Compact

theorem exists_superlevel_subset_of_unique_max {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) {q : X} (hmax : ∀ x : X, x ≠ q → f x < f q)
    {U : Set X} (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, f q - δ ≤ f x → x ∈ U := by
  by_cases hne : (Uᶜ).Nonempty
  · obtain ⟨x₀, hx₀U, hx₀max⟩ :=
      hU.isClosed_compl.isCompact.exists_isMaxOn hne hf.continuousOn
    have hx₀Unot : x₀ ∉ U := by simpa using hx₀U
    have hx₀ne : x₀ ≠ q := fun h => hx₀Unot (h ▸ hqU)
    have hx₀lt : f x₀ < f q := hmax x₀ hx₀ne
    refine ⟨(f q - f x₀) / 2, by linarith, ?_⟩
    intro x hx
    by_contra hxU
    have hxU' : x ∈ Uᶜ := by simpa using hxU
    have hle : f x ≤ f x₀ := hx₀max hxU'
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x _
    by_contra hxU
    exact hne ⟨x, by simpa using hxU⟩

end Commons.Topology.Compact