import Mathlib

open Filter Topology

set_option linter.unusedVariables false

namespace Work.Drive

/-- **The uniform "the perturbation does not leave a compact set" statement.** -/
theorem exists_pos_norm_le_mem_of_compact {m : ℕ} {X : Type*} [TopologicalSpace X]
    (Ξ : EuclideanSpace ℝ (Fin m) → X → X)
    (hcont : Continuous fun q : EuclideanSpace ℝ (Fin m) × X => Ξ q.1 q.2)
    (h0 : ∀ x : X, Ξ 0 x = x)
    {K0 K1 S : Set X} (hK0 : IsClosed K0) (hK1 : IsClosed K1) (hS : IsCompact S)
    (hsub : K0 ⊆ interior K1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : EuclideanSpace ℝ (Fin m)) (x : X), ‖p‖ ≤ ε → x ∈ S →
      Ξ p x ∈ K0 → x ∈ K1 := by
  by_contra hcon
  push Not at hcon
  -- for every `n` there is a "bad" configuration with `‖p‖ ≤ 1/(n+1)`
  have hbad : ∀ n : ℕ, ∃ (p : EuclideanSpace ℝ (Fin m)) (x : X),
      ‖p‖ ≤ (1 : ℝ) / (n + 1) ∧ x ∈ S ∧ Ξ p x ∈ K0 ∧ x ∉ K1 := by
    intro n
    obtain ⟨p, x, hp, hxS, hK, hxK⟩ := hcon ((1 : ℝ) / (n + 1)) (by positivity)
    exact ⟨p, x, hp, hxS, hK, hxK⟩
  choose p x hp hxS hKmem hxK1 using hbad
  -- the product `closedBall 0 1 ×ˢ S` is compact and contains all the bad configurations
  have hTcomp : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ S) :=
    (isCompact_closedBall 0 1).prod hS
  have hmem : ∀ n : ℕ, (p n, x n) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ S := by
    intro n
    refine ⟨?_, hxS n⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖p n‖ ≤ (1 : ℝ) / (n + 1) := hp n
    have h2 : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    linarith
  have hle : Filter.map (fun n => (p n, x n)) Filter.atTop ≤
      𝓟 (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ S) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Filter.Eventually.of_forall hmem
  -- extract a cluster point of the bad configurations
  obtain ⟨q, _hqT, hcl⟩ := hTcomp hle
  have hcl1 : ClusterPt q.1 (Filter.map (fun n => p n) Filter.atTop) := by
    have h := hcl.map (continuous_fst.continuousAt (x := q))
      (le_refl (Filter.map (Prod.fst) (Filter.map (fun n => (p n, x n)) Filter.atTop)))
    simpa [Filter.map_map, Function.comp_def] using h
  have hp_tend : Filter.Tendsto (fun n : ℕ => p n) Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hp n) ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the parameters converge to `0`, so the first coordinate of the cluster point is `0`
  have hq1 : q.1 = 0 := by
    have hnb : NeBot (𝓝 q.1 ⊓ 𝓝 (0 : EuclideanSpace ℝ (Fin m))) := hcl1.mono hp_tend
    by_contra hne
    rw [disjoint_iff.mp (disjoint_nhds_nhds.mpr hne)] at hnb
    exact hnb.ne rfl
  -- `K0` is closed, so the cluster point lands in `K0`, i.e. (as `Ξ 0 = id`) `q.2 ∈ K0`
  have hmap : MapClusterPt (Ξ q.1 q.2) Filter.atTop (fun n => Ξ (p n) (x n)) := by
    have h := hcl.map hcont.continuousAt
      (le_refl (Filter.map (fun w : EuclideanSpace ℝ (Fin m) × X => Ξ w.1 w.2)
        (Filter.map (fun n => (p n, x n)) Filter.atTop)))
    simpa [MapClusterPt, Filter.map_map, Function.comp_def] using h
  have hK0q : Ξ q.1 q.2 ∈ K0 :=
    hK0.mem_of_mapClusterPt hmap (Filter.Eventually.of_forall hKmem)
  have hq2K0 : q.2 ∈ K0 := by simpa [hq1, h0] using hK0q
  have hq2int : q.2 ∈ interior K1 := hsub hq2K0
  -- but `q.2` is also a cluster point of points lying outside `K1`
  have hcl2 : ClusterPt q.2 (Filter.map (fun n => x n) Filter.atTop) := by
    have h := hcl.map (continuous_snd.continuousAt (x := q))
      (le_refl (Filter.map (Prod.snd) (Filter.map (fun n => (p n, x n)) Filter.atTop)))
    simpa [Filter.map_map, Function.comp_def] using h
  have hfreq : ∃ᶠ n in Filter.atTop, x n ∈ interior K1 :=
    Filter.frequently_map.mp (hcl2.frequently (isOpen_interior.mem_nhds hq2int))
  obtain ⟨n, hn⟩ := hfreq.exists
  exact hxK1 n (interior_subset hn)

/-!
Proof sketch: if the conclusion failed there would be `p n → 0` and `x n ∈ S` with
`Ξ (p n) (x n) ∈ K0` and `x n ∉ K1` for every `n`. The bad configurations `(p n, x n)` lie in the
compact set `closedBall 0 1 ×ˢ S`, so they have a cluster point `q`. Since `K0` is closed and
`q ↦ Ξ q.1 q.2` is continuous, `Ξ q.1 q.2 ∈ K0`; since `p n → 0`, the first coordinate of `q` is `0`,
so `q.2 = Ξ q.1 q.2 ∈ K0 ⊆ interior K1`. But `q.2` is a cluster point of the sequence `x n`, which
lies outside `K1`, while `interior K1` is a neighbourhood of `q.2`; hence `x n ∈ interior K1 ⊆ K1`
for some `n`, a contradiction. (Note that `hK1` is not needed: only `hsub` and the openness of the
interior of `K1` are used.) -/

end Work.Drive
