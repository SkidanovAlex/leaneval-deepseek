import Mathlib
import Submission.Commons.Topology.continuous_root_of_strictMono

namespace Commons.Topology

open Filter Set
open scoped _root_.Topology

/-- **Continuity within a set of a point determined by two unique distance equations.**

Let `M` be a compact pseudo-emetric space, `s ⊆ Z`, and `z₀ ∈ s`.  Suppose that along `s`:
`a → a z₀`, `α → α z₀`, `β → β z₀`, and that for every `z ∈ s` the point `g z` satisfies
`edist p (g z) = α z` and `edist (a z) (g z) = β z`.  If the pair of distance equations at `z₀`
has the *unique* solution `y₀`, then `g z₀ = y₀` and `g` is continuous within `s` at `z₀`.

The proof is the compactness/closed-graph argument: any cluster point `x` of `g` along `𝓝[s] z₀`
inherits both distance equations at `z₀` (each is a limit of a closed relation), hence equals
`y₀`; a map in a compact space whose (map)cluster points are all equal to `y₀` tends to `y₀`. -/
theorem continuousWithinAt_of_unique_edist_eq
    {Z : Type*} [TopologicalSpace Z] {M : Type*} [PseudoEMetricSpace M] [CompactSpace M]
    {s : Set Z} {p : M} {a g : Z → M} {α β : Z → ENNReal} {z₀ : Z} {y₀ : M}
    (hz₀ : z₀ ∈ s)
    (ha : ContinuousWithinAt a s z₀) (hα : ContinuousWithinAt α s z₀)
    (hβ : ContinuousWithinAt β s z₀)
    (hg : ∀ z ∈ s, edist p (g z) = α z ∧ edist (a z) (g z) = β z)
    (huniq : ∀ y : M, edist p y = α z₀ → edist (a z₀) y = β z₀ → y = y₀) :
    g z₀ = y₀ ∧ ContinuousWithinAt g s z₀ := by
  have hz : g z₀ = y₀ := huniq (g z₀) (hg z₀ hz₀).1 (hg z₀ hz₀).2
  refine ⟨hz, ?_⟩
  show Tendsto g (𝓝[s] z₀) (𝓝 (g z₀))
  rw [hz]
  refine tendsto_nhds_of_unique_mapClusterPt (l := 𝓝[s] z₀) (y := y₀) (f := g) fun x hx =>
    huniq x ?_ ?_
  · -- first equation: `edist p x = α z₀`
    have hclosed : IsClosed {q : ENNReal × ENNReal | q.1 = q.2} :=
      isClosed_eq continuous_fst continuous_snd
    have hy : MapClusterPt (edist p x) (𝓝[s] z₀) (fun z => edist p (g z)) :=
      hx.continuousAt_comp (Continuous.edist continuous_const continuous_id).continuousAt
    have hmem : ∀ᶠ z in 𝓝[s] z₀,
        (α z, edist p (g z)) ∈ {q : ENNReal × ENNReal | q.1 = q.2} := by
      filter_upwards [self_mem_nhdsWithin] with z hzs
      exact ((hg z hzs).1).symm
    have h := mem_of_mapClusterPt_of_tendsto hclosed hα hy hmem
    simpa using h.symm
  · -- second equation: `edist (a z₀) x = β z₀`
    have hclosed : IsClosed {q : (M × ENNReal) × M | edist q.1.1 q.2 = q.1.2} := by
      apply isClosed_eq
      · exact Continuous.edist continuous_fst.fst continuous_snd
      · exact continuous_fst.snd
    have hφ : Tendsto (fun z => (a z, β z)) (𝓝[s] z₀) (𝓝 (a z₀, β z₀)) := by
      rw [nhds_prod_eq]
      exact Tendsto.prodMk ha hβ
    have hmem : ∀ᶠ z in 𝓝[s] z₀,
        ((a z, β z), g z) ∈ {q : (M × ENNReal) × M | edist q.1.1 q.2 = q.1.2} := by
      filter_upwards [self_mem_nhdsWithin] with z hzs
      exact (hg z hzs).2
    have h := mem_of_mapClusterPt_of_tendsto hclosed hφ hx hmem
    simpa using h

end Commons.Topology
