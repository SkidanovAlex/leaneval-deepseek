import Mathlib

namespace Commons.Analysis.InfiniteSum

/-- If a function `f : ℂ → ℂ` has unconditional sum `a`, and a family of finite sets
`S T` eventually contains every point of the support of `f`, then the partial sums
`∑_{u ∈ S T} f u` converge to `a` along `T → ∞`. -/
theorem hasSum_tendsto_finset_sum {f : ℂ → ℂ} {a : ℂ} (hf : HasSum f a) {S : ℝ → Finset ℂ}
    (hS : ∀ u : ℂ, f u ≠ 0 → Filter.Eventually (fun T : ℝ => u ∈ S T) Filter.atTop) :
    Filter.Tendsto (fun T : ℝ => Finset.sum (S T) (fun u : ℂ => f u)) Filter.atTop (nhds a) := by
  have hf_tend : Filter.Tendsto (fun s : Finset ℂ => ∑ u ∈ s, f u) Filter.atTop (nhds a) := hf
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf' : ∀ᶠ (s : Finset ℂ) in Filter.atTop, dist (∑ u ∈ s, f u) a < ε :=
    (Metric.tendsto_nhds.mp hf_tend) ε hε
  rw [Filter.eventually_atTop] at hf'
  obtain ⟨s₀, hs₀⟩ := hf'
  set s₁ : Finset ℂ := s₀.filter (fun u => f u ≠ 0) with hs₁
  have hmem_s₁ : ∀ u ∈ s₁, f u ≠ 0 := by
    intro u hu
    rw [hs₁, Finset.mem_filter] at hu
    exact hu.2
  have hfin : ∀ᶠ T in Filter.atTop, ∀ u ∈ s₁, u ∈ S T := by
    rw [Finset.eventually_all]
    intro u hu
    exact hS u (hmem_s₁ u hu)
  rw [Filter.eventually_atTop] at hfin
  obtain ⟨T₀, hT₀⟩ := hfin
  rw [Filter.eventually_atTop]
  refine ⟨T₀, fun T hT => ?_⟩
  have hsub : s₁ ⊆ S T := hT₀ T hT
  have hzero : ∀ x ∈ S T ∪ s₀, x ∉ S T → f x = 0 := by
    intro x hx hxnot
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact absurd hx hxnot
    · by_contra hfx
      have hxs₁ : x ∈ s₁ := by
        rw [hs₁, Finset.mem_filter]
        exact ⟨hx, hfx⟩
      exact hxnot (hsub hxs₁)
  have hsum_eq : ∑ u ∈ S T, f u = ∑ u ∈ S T ∪ s₀, f u :=
    Finset.sum_subset Finset.subset_union_left hzero
  rw [hsum_eq]
  exact hs₀ (S T ∪ s₀) Finset.subset_union_right

end Commons.Analysis.InfiniteSum
