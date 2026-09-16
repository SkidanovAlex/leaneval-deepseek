import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.ValuationTopology

open scoped Topology WithZero
open Filter

namespace Commons.Topology.Algebra.Valued

/-- Domination of valuations preserves summability, for a valuation with values in an arbitrary
linearly ordered commutative group with zero (the `ℤᵐ⁰` case is
`Commons.Topology.Algebra.Valued.summable_of_v_le`). -/
theorem summable_of_v_le_general {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [CompleteSpace K] [NonarchimedeanAddGroup K] {α : Type*} {f g : α → K}
    (hg : Summable g) (h : ∀ a, Valued.v (f a) ≤ Valued.v (g a)) : Summable f := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at hg ⊢
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, -, hγU⟩ :=
    (Valued.hasBasis_nhds_zero K Γ₀).mem_iff.mp hU
  have hball : {x : K | Valued.v.restrict x < (γ : _)} ∈ 𝓝 (0 : K) :=
    (Valued.hasBasis_nhds_zero K Γ₀).mem_iff.mpr
      ⟨γ, trivial, subset_rfl⟩
  filter_upwards [hg.eventually hball] with a ha
  refine hγU (show Valued.v.restrict (f a) < (γ : _) from ?_)
  rw [Valuation.restrict_lt_iff_lt_embedding] at ha ⊢
  exact lt_of_le_of_lt (h a) ha

end Commons.Topology.Algebra.Valued