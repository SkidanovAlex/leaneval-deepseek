import Mathlib

open scoped Topology
open Filter

namespace Work.Drive.Slab

/-- **The germ of injectivity along a compact set.**

If `g : M → ℝⁿ` is continuous, *locally injective* (every point has an open neighbourhood on which
`g` is injective) and injective on a **compact** set `K`, then there is an open `U ⊇ K` on which `g`
is still injective.  (Both reviewers of the first version correctly insisted on `IsCompact K`: for a
merely non-closed `K`, e.g. a dense antipodally-free subset of `S¹` with `g = z²`, no such `U`
exists.)

This is the tube/graph-piece step of the slab construction: applied to `g = β ∘ f` along a path lying
in the flat set `V` of the finger — where the base map is a local diffeomorphism
(`Work.Drive.Slab.isLocalDiffeomorphAt_base_of_slab`) and injective
(`Work.Drive.Slab.injOn_base_of_finger`) — it produces an open tube around the path on which the
height `θ ∘ f` is a function of the base, i.e. the pinned-graph datum of the drive.

(For the intended application `M` is a compact manifold; a compatible pseudo-metric instance is
supplied by `TopologicalSpace.pseudoMetrizableSpacePseudoMetric`, so the pseudo-metric hypothesis is
not a restriction, but it keeps the proof sequence-based.) -/
theorem compactInjOnTube {n : ℕ} {M : Type*} [PseudoMetricSpace M] [T2Space M] [CompactSpace M]
    (g : M → EuclideanSpace ℝ (Fin n)) (hg : Continuous g) (K : Set M) (hK : IsCompact K)
    (hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn g U)
    (hinj : Set.InjOn g K) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ Set.InjOn g U := by
  -- The empty case is trivial.
  rcases Set.eq_empty_or_nonempty K with rfl | hKne
  · exact ⟨∅, isOpen_empty, Set.empty_subset _, Set.injOn_empty g⟩
  -- Main claim: the injectivity of `g` on `K` propagates to the tube of points whose
  -- `infDist` to `K` is small.
  have hmain : ∃ δ > 0, ∀ x y : M,
      Metric.infDist x K < δ → Metric.infDist y K < δ → g x = g y → x = y := by
    by_contra hbad
    push Not at hbad
    -- A sequence of "bad pairs", both coordinates within `1/(m+1)` of `K`.
    have hseq : ∀ m : ℕ, ∃ q : M × M, Metric.infDist q.1 K < ((m : ℝ) + 1)⁻¹ ∧
        Metric.infDist q.2 K < ((m : ℝ) + 1)⁻¹ ∧ g q.1 = g q.2 ∧ q.1 ≠ q.2 := by
      intro m
      obtain ⟨x, y, h1, h2, hg', hne⟩ := hbad ((m : ℝ) + 1)⁻¹ (by positivity)
      exact ⟨(x, y), h1, h2, hg', hne⟩
    choose p hp using hseq
    -- Compactness of `M` extracts a convergent subsequence of the pairs.
    obtain ⟨ab, -, φ, hφmono, hφtend⟩ :=
      isCompact_univ.tendsto_subseq (x := p) (fun _ => Set.mem_univ _)
    obtain ⟨hx, hy⟩ := (Prod.tendsto_iff (p ∘ φ) ab).mp hφtend
    -- `1/(φ m + 1) → 0`.
    have hc0 : Filter.Tendsto (fun m : ℕ => ((φ m : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun m : ℕ => (φ m : ℝ) + 1) Filter.atTop Filter.atTop :=
        (tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop).atTop_add tendsto_const_nhds
      exact tendsto_inv_atTop_zero.comp h1
    have hca : Filter.Tendsto (fun m => Metric.infDist (p (φ m)).1 K) Filter.atTop
        (𝓝 (Metric.infDist ab.1 K)) :=
      ((Metric.continuous_infDist_pt K).tendsto ab.1).comp hx
    have hcb : Filter.Tendsto (fun m => Metric.infDist (p (φ m)).2 K) Filter.atTop
        (𝓝 (Metric.infDist ab.2 K)) :=
      ((Metric.continuous_infDist_pt K).tendsto ab.2).comp hy
    -- Both limits lie in `K`.
    have hle_a : Metric.infDist ab.1 K ≤ 0 :=
      le_of_tendsto_of_tendsto' hca hc0 (fun m => le_of_lt (hp (φ m)).1)
    have hle_b : Metric.infDist ab.2 K ≤ 0 :=
      le_of_tendsto_of_tendsto' hcb hc0 (fun m => le_of_lt (hp (φ m)).2.1)
    have hza : Metric.infDist ab.1 K = 0 := le_antisymm hle_a Metric.infDist_nonneg
    have hzb : Metric.infDist ab.2 K = 0 := le_antisymm hle_b Metric.infDist_nonneg
    have hKa : ab.1 ∈ K :=
      hK.isClosed.closure_eq ▸ (Metric.mem_closure_iff_infDist_zero hKne).mpr hza
    have hKb : ab.2 ∈ K :=
      hK.isClosed.closure_eq ▸ (Metric.mem_closure_iff_infDist_zero hKne).mpr hzb
    -- Their `g`-images agree, so by injectivity on `K` the two limits coincide.
    have hfun : (fun m => g ((p (φ m)).1)) = (fun m => g ((p (φ m)).2)) :=
      funext fun m => (hp (φ m)).2.2.1
    have hga : Filter.Tendsto (fun m => g ((p (φ m)).1)) Filter.atTop (𝓝 (g ab.1)) :=
      (hg.tendsto ab.1).comp hx
    have hgb : Filter.Tendsto (fun m => g ((p (φ m)).2)) Filter.atTop (𝓝 (g ab.2)) :=
      (hg.tendsto ab.2).comp hy
    rw [hfun] at hga
    have hgab : g ab.1 = g ab.2 := tendsto_nhds_unique hga hgb
    have hab : ab.1 = ab.2 := hinj hKa hKb hgab
    -- Local injectivity at the common limit kills the bad pairs.
    obtain ⟨U₀, hU₀o, hab1, hU₀inj⟩ := hloc ab.1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU₀o.mem_nhds hab1)
    have hy' : Filter.Tendsto (fun m => (p (φ m)).2) Filter.atTop (𝓝 ab.1) := hab.symm ▸ hy
    have evx : ∀ᶠ m in Filter.atTop, (p (φ m)).1 ∈ Metric.ball ab.1 ε :=
      hx.eventually (Metric.ball_mem_nhds ab.1 hε)
    have evy : ∀ᶠ m in Filter.atTop, (p (φ m)).2 ∈ Metric.ball ab.1 ε :=
      hy'.eventually (Metric.ball_mem_nhds ab.1 hε)
    obtain ⟨k, hkx, hky⟩ := (evx.and evy).exists
    exact (hp (φ k)).2.2.2 (hU₀inj (hball hkx) (hball hky) (hp (φ k)).2.2.1)
  -- The tube around `K`.
  obtain ⟨δ, hδ, hmain⟩ := hmain
  exact ⟨{x | Metric.infDist x K < δ},
    isOpen_lt (Metric.continuous_infDist_pt K) continuous_const,
    fun x hx => by show Metric.infDist x K < δ; rw [Metric.infDist_zero_of_mem hx]; exact hδ,
    fun x hx y hy hxy => hmain x y hx hy hxy⟩

end Work.Drive.Slab
