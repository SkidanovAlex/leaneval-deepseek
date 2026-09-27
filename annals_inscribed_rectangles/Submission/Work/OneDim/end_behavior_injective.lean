import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.cluster_points_atTop_injective

/-!
# The unique cluster point at `+∞` of an injective curve in a 1-manifold is its limit

Let `γ : ℝ → C` be a continuous injective curve into a Hausdorff 1-manifold `C`.  Suppose `x` is
a cluster point of `γ` at `+∞`, i.e. every open neighbourhood of `x` is met at arbitrarily large
times.  Then `γ t → x` as `t → +∞`.

The proof is local and avoids any classification of 1-manifolds.  Take a chart-ball `N` around `x`
inside a prescribed neighbourhood.  In the chart, `∂N` corresponds to a sphere in `ℝ¹`, hence is
contained in a two-point set; since `γ` is injective it can hit `∂N` at most twice, so there is a
last time `T` spent on `∂N`.  Beyond `T` the curve avoids `∂N`, and `C \ ∂N` is the disjoint union
of the two open sets `N` and `(closure N)ᶜ`; the connected tail `γ '' (T, ∞)` must therefore lie in
one of them.  It cannot lie in `(closure N)ᶜ`, because `hx` produces arbitrarily large times with
`γ t ∈ N`.  Hence `γ` is eventually in `N`.
-/

namespace Work.OneDim

open scoped Manifold
open Set Topology Filter

theorem end_behavior_injective {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C] [T2Space C] [SecondCountableTopology C]
    {γ : ℝ → C} (hγ : Continuous γ) (hinj : Function.Injective γ) {x : C}
    (hx : ∀ U : Set C, IsOpen U → x ∈ U →
      Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atTop) :
    Filter.Tendsto γ Filter.atTop (nhds x) := by
  classical
  -- A chart at `x` and a radius whose closed ball lies inside the chart target.
  obtain ⟨φ, r, hxsrc, hr, hrsub⟩ :
      ∃ (φ : OpenPartialHomeomorph C E1) (r : ℝ),
        x ∈ φ.source ∧ 0 < r ∧ Metric.closedBall (φ x) r ⊆ φ.target := by
    refine ⟨chartAt E1 x, ?_⟩
    set φ₀ := chartAt E1 x with hφ₀
    have hxsrc : x ∈ φ₀.source := mem_chart_source _ _
    obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (φ₀.open_target.mem_nhds (φ₀.map_source hxsrc))
    exact ⟨ε, hxsrc, hε, hεsub⟩
  have hxφ : φ.symm (φ x) = x := φ.left_inv hxsrc
  rw [Filter.tendsto_def]
  intro V hV
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hV
  -- Choose a chart ball `N` around `x` lying inside `s`.
  have hmap : φ x ∈ φ.target := φ.map_source hxsrc
  have hpre : φ.symm ⁻¹' s ∈ 𝓝 (φ x) := by
    have : s ∈ 𝓝 (φ.symm (φ x)) := by rw [hxφ]; exact hs_open.mem_nhds hxs
    exact (φ.continuousAt_symm hmap).preimage_mem_nhds this
  obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_ball.mem_iff.mp hpre
  set ρ := min ε r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hε hr
  have hρle_r : ρ ≤ r := by rw [hρdef]; exact min_le_right _ _
  have hρle_ε : ρ ≤ ε := by rw [hρdef]; exact min_le_left _ _
  have hclosed_sub : Metric.closedBall (φ x) ρ ⊆ φ.target :=
    (Metric.closedBall_subset_closedBall hρle_r).trans hrsub
  set N : Set C := φ.source ∩ φ ⁻¹' Metric.ball (φ x) ρ with hNdef
  set K : Set C := φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) ρ with hKdef
  have hN_eq : N = φ.symm '' Metric.ball (φ x) ρ := by
    rw [hNdef]
    exact (φ.symm_image_eq_source_inter_preimage
      (Metric.ball_subset_closedBall.trans hclosed_sub)).symm
  have hK_eq : K = φ.symm '' Metric.closedBall (φ x) ρ := by
    rw [hKdef]
    exact (φ.symm_image_eq_source_inter_preimage hclosed_sub).symm
  have hNopen : IsOpen N := by
    rw [hNdef]; exact φ.isOpen_inter_preimage Metric.isOpen_ball
  have hNs : N ⊆ s := by
    rw [hN_eq]
    rintro z ⟨w, hw, rfl⟩
    exact hεsub (Metric.ball_subset_ball hρle_ε hw)
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      (φ.symm.continuousOn_toFun.mono hclosed_sub)
  have hNsubK : N ⊆ K := by
    rw [hNdef, hKdef]
    exact Set.inter_subset_inter le_rfl (preimage_mono Metric.ball_subset_closedBall)
  have hclN : closure N ⊆ K := closure_minimal hNsubK hKcompact.isClosed
  have hxN : x ∈ N := by
    rw [hNdef]
    exact ⟨hxsrc, Metric.mem_ball_self hρpos⟩
  -- The boundary of `N` is contained in a two-point set.
  have hboundary : ∀ z ∈ closure N \ N,
      z ∈ ({φ.symm (φ x + ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1),
        φ.symm (φ x - ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1)} : Set C) := by
    rintro z ⟨hzcl, hzN⟩
    have hzK : z ∈ K := hclN hzcl
    rw [hKdef] at hzK
    have hzsource : z ∈ φ.source := hzK.1
    have hzcb : φ z ∈ Metric.closedBall (φ x) ρ := hzK.2
    have hznb : φ z ∉ Metric.ball (φ x) ρ := by
      intro hb
      exact hzN (by rw [hNdef]; exact ⟨hzsource, hb⟩)
    have hzsphere : φ z ∈ Metric.sphere (φ x) ρ := by
      rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hzcb)
        (le_of_not_gt fun hh => hznb (Metric.mem_ball.mpr hh))
    rcases sphere_fin_one_subset (φ x) ρ hzsphere with h | h
    · left; rw [← φ.left_inv hzsource, h]
    · right; rw [← φ.left_inv hzsource, h]; simp
  -- At most two times lie on the boundary, hence they are bounded above.
  set S : Set ℝ := {t | γ t ∈ closure N \ N} with hSdef
  have hSfin : S.Finite := by
    have hsub : S ⊆ γ ⁻¹' ({φ.symm (φ x + ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1),
        φ.symm (φ x - ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1)} : Set C) :=
      fun t ht => hboundary (γ t) ht
    refine (Set.Finite.preimage (hinj.injOn) ?_).subset hsub
    exact (Set.finite_singleton
      (φ.symm (φ x - ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1))).insert
      (φ.symm (φ x + ρ • EuclideanSpace.single (𝕜 := ℝ) 0 1))
  obtain ⟨T, hT⟩ := hSfin.bddAbove
  -- Past `T` the curve stays in one of the two pieces of `C \ ∂N`.
  have hconn : IsPreconnected (γ '' Set.Ioi T) :=
    isPreconnected_Ioi.image γ hγ.continuousOn
  have hsub : γ '' Set.Ioi T ⊆ N ∪ (closure N)ᶜ := by
    rintro z ⟨t, ht, rfl⟩
    have htS : t ∉ S := by
      intro hmem
      have hle : t ≤ T := hT hmem
      exact absurd hle (not_le.mpr ht)
    by_cases hzN : γ t ∈ N
    · exact Or.inl hzN
    · exact Or.inr fun hzcl => htS ⟨hzcl, hzN⟩
  have hdisj : Disjoint N (closure N)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2 (subset_closure hz1)
  have hN_eventually : ∀ᶠ t in Filter.atTop, γ t ∈ N := by
    rcases IsPreconnected.subset_or_subset hNopen isClosed_closure.isOpen_compl hdisj hsub hconn
      with h | h
    · exact Filter.eventually_atTop.mpr ⟨T + 1, fun b hb =>
        h ⟨b, by rw [Set.mem_Ioi]; linarith, rfl⟩⟩
    · exfalso
      obtain ⟨b, hb, hγb⟩ := (Filter.frequently_atTop.mp (hx N hNopen hxN)) (T + 1)
      exact h ⟨b, by rw [Set.mem_Ioi]; linarith, rfl⟩ (subset_closure hγb)
  exact Filter.mem_of_superset hN_eventually (Set.preimage_mono (hNs.trans hs_sub))

end Work.OneDim
