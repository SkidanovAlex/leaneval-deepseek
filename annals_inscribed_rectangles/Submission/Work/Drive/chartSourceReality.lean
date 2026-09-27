import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.sweepTripleGeneric

/-!
# The chart-source reality of the parametric Sard's hypotheses (the `hloc` obligation)

The reference-triple genericity lemma of the `hn2` lane,
`Work.Drive.exists_meet3Hyp_and_goodAt_refTriple` (`Submission/Work/Drive/refTripleGeneric.lean`),
takes a chart centre `p : CappingSpace` and the hypothesis

> `hloc : ∀ y ∈ unitBox 8, meet3 (G 0) y → ∀ k, G 0 k (bPartC k y) ∈ (chr p).source`

("the base triple locus lies in the source of the chart at `p`"), and the only residual input of the
parametric Sard `Work.Drive.exists_meet3Hyp_of_good_family` is the pair of hypotheses

> `hbase : ∀ y ∈ unitBox 8, meet3 (G 0) y → y ∈ interior K`  and
> `hcontain : ∀ t, ‖t‖ < ε → y ∈ K → ∀ k, G t k (bPartC k y) ∈ (chr p).source`.

This file records two facts that determine what can and cannot be done with them.

## 1. What `(chr p).source` is

For the transparent structure `Work.Drive.cappingCharted`
(`Homeomorph.chartedSpace cappingSpaceHomeoProj.symm`), the preferred chart at `p` is

`(chartAt (Eucl 4) p : OpenPartialHomeomorph CappingSpace (Eucl 4)) = L ≫ₕ C` with
`L = (choose).symm` the chosen local inverse of `cappingSpaceHomeoProj.symm` at `p` and
`C = chartAt halfLine (cappingSpaceHomeoProj p)`; the *source* of the chart is therefore

`(chr p).source = L.source ∩ L ⁻¹' C.source`,

where `L.source = ((choose) : OpenPartialHomeomorph _ _).target` is the image of the *chosen* open
neighbourhood of `p` under the homeomorphism, i.e. an **opaque open neighbourhood of `p`**:
`Classical.choose` does not reduce on the constructor `⟨_, trivial, rfl⟩` of
`Homeomorph.isLocalHomeomorph`, and Mathlib's `IsLocalHomeomorph.localInverseAt` records no
description of the chosen source.  Consequently the *only* membership in `(chr p).source` that is
provable for an arbitrary point is the one at the centre (`mem_chart_source`), and the statements
`hloc`, `hresQ`, `hresV`, `hresW` (the transport lane) can only be discharged

* for the centre itself, or
* through the *germ* forms of the chart (`Work.Drive.eventuallyEq_chartAt_homeomorph_chartedSpace`,
  whose `_self` case needs no hypothesis).

No class-side description of `(chr p).source` — in particular not "the class of the point lies in
`projChartSource i`" — is available: the class coordinate is only *one* of the two factors and the
other one (`L.source`) has no description.

## 2. What is enough, and what is provable

The Sard's chart hypotheses are therefore *equivalent* to `hloc` (see
`Work.Drive.exists_compact_and_eps_of_chartResident`): from "the base values lie in `(chr p).source`"
one *does* get a compact `K` and an `ε > 0` with `hbase`/`hcontain`, by compactness of the base locus
(a closed subset of the box), openness of the chart source and continuity of the family.  What remains
geometric is only the base-value condition, and the clean sufficient condition for it — the one that
needs no knowledge of the chart at all — is

> **the base triple locus has a single value**, i.e. all `G 0 k (bPartC k y)` at base points `y` are
> equal to one fixed point `p` (`Work.Drive.hloc_of_single_value`).

That case is then *immediate* (take the chart centred at `p`; `mem_chart_source`).  In particular the
`hloc` obligation of the reference triple is a statement about the *geometry* of the three sweeps (the
base locus must be a single point, or at least carry a single value), **not** about the chart: any
plan that discharges `hloc` by describing the chart's source has no formal counterpart.
-/

namespace Work.Drive

open Manifold Set Metric Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The chart source contains a neighbourhood of its centre -/

/-- **The source of the chart at `p` is a neighbourhood of `p`.** -/
theorem exists_nhds_subset_chartAt_source
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (p : M) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ U ⊆ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source :=
  ⟨_, (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).open_source.mem_nhds
      (mem_chart_source (EuclideanSpace ℝ (Fin 4)) p), subset_rfl⟩

/-! ## 2. The base locus is closed -/

/-- **The triple intersection set of three continuous chains is closed.** -/
theorem isClosed_meet3 {M : Type*} [TopologicalSpace M] [T2Space M]
    {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} (h : ∀ k : Fin 3, Continuous (D k)) :
    IsClosed {x : EuclideanSpace ℝ (Fin 9) | Work.Drive.TParity.meet3 D x} := by
  have hc : ∀ k : Fin 3, Continuous fun x : EuclideanSpace ℝ (Fin 9) =>
      D k (Work.Drive.TParity.bPartC k x) := fun k =>
    (h k).comp (Work.Drive.TParity.bPartC k).continuous
  have hset : {x : EuclideanSpace ℝ (Fin 9) | Work.Drive.TParity.meet3 D x}
      = {x | D 0 (Work.Drive.TParity.bPartC 0 x) = D 1 (Work.Drive.TParity.bPartC 1 x)}
        ∩ {x | D 0 (Work.Drive.TParity.bPartC 0 x) = D 2 (Work.Drive.TParity.bPartC 2 x)} := by
    ext x
    simp [Work.Drive.TParity.meet3]
  rw [hset]
  exact (isClosed_eq (hc 0) (hc 1)).inter (isClosed_eq (hc 0) (hc 2))

/-! ## 3. The reduction: chart-resident base values give the Sard's `K`, `ε` -/

/-- **The Sard's chart hypotheses, from the chart-residency of the base values.**

For a charted `4`-manifold `M`, a family `G` of triples of chains, jointly continuous in the parameter
and the point, and a chart centre `p` such that every *base* value `G 0 k (bPartC k y)` lies in
`(chr p).source`, there are a compact `K` and an `ε > 0` with

* the base locus in the interior of `K`, and
* all values `G t k (bPartC k y)` with `‖t‖ < ε` and `y ∈ K` in `(chr p).source`

— i.e. exactly the `hbase` and `hcontain` of `Work.Drive.exists_meet3Hyp_of_good_family`. -/
theorem exists_compact_and_eps_of_chartResident
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M)
    (hcont : ∀ k : Fin 3, Continuous
      fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2)
    (hres : ∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 (G 0) y →
      ∀ k : Fin 3, G 0 k (Work.Drive.TParity.bPartC k y)
        ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (ε : ℝ), IsCompact K ∧ 0 < ε ∧
      (∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 (G 0) y → y ∈ interior K) ∧
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y)
          ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source) := by
  classical
  set S : Set M := (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source with hS
  have hSopen : IsOpen S := (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).open_source
  -- the joint preimage of the chart source is open
  have hWopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ S} := by
    rw [show {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
          ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ S}
        = ⋂ k : Fin 3, {q | G q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ S} from by
      ext q; simp [Set.mem_iInter]]
    refine isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (q.1, Work.Drive.TParity.bPartC k q.2) :=
      continuous_fst.prodMk ((Work.Drive.TParity.bPartC k).continuous.comp continuous_snd)
    exact ((hcont k).comp hc).isOpen_preimage S hSopen
  -- the base locus
  set B : Set (EuclideanSpace ℝ (Fin 9)) :=
    {y | y ∈ Submission.Drive.unitBox 8 ∧ Work.Drive.TParity.meet3 (G 0) y} with hB
  have hBclosed : IsClosed B := by
    rw [hB]
    refine (isClosed_unitBox 8).inter (isClosed_meet3 ?_)
    intro k
    exact (hcont k).comp (continuous_const.prodMk continuous_id)
  have hBcomp : IsCompact B :=
    (isCompact_unitBox 8).of_isClosed_subset hBclosed fun _ hy => hy.1
  -- for every base point a product neighbourhood of `(0, y)` inside the joint preimage
  have hpt : ∀ y : {y // y ∈ B}, ∃ r : ℝ, 0 < r ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ (t : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin 9)),
          ‖t‖ < r → x ∈ Metric.ball (y : EuclideanSpace ℝ (Fin 9)) ρ →
            ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k x) ∈ S := by
    intro y
    have hmem : ((0 : EuclideanSpace ℝ (Fin m)), (y : EuclideanSpace ℝ (Fin 9)))
        ∈ {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
            ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ S} := fun k =>
      hres y.1 y.2.1 y.2.2 k
    have hmem' : ({q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
        ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ S})
        ∈ 𝓝 ((0 : EuclideanSpace ℝ (Fin m)), (y : EuclideanSpace ℝ (Fin 9))) :=
      hWopen.mem_nhds hmem
    rw [nhds_prod_eq] at hmem'
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hmem'
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨r, hr, ρ, hρ, ?_⟩
    intro t x ht hx k
    have hxV : x ∈ V := hρV hx
    have htU : t ∈ U := hrU (by rw [Metric.mem_ball, dist_zero_right]; exact ht)
    have hmemUV : ((t, x) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9))
        ∈ U ×ˢ V := Set.mem_prod.mpr ⟨htU, hxV⟩
    exact hUV hmemUV k
  choose r hr ρ hρ hW using hpt
  -- the balls of half radius around the base points cover the base locus
  obtain ⟨s, hs⟩ := hBcomp.elim_finite_subcover
    (fun i : {y // y ∈ B} => Metric.ball (i : EuclideanSpace ℝ (Fin 9)) (ρ i / 2))
    (fun _ => Metric.isOpen_ball)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      show y ∈ Metric.ball y (ρ ⟨y, hy⟩ / 2)
      rw [Metric.mem_ball, dist_self]
      exact half_pos (hρ ⟨y, hy⟩)⟩)
  -- the open neighbourhood of the base locus
  set U : Set (EuclideanSpace ℝ (Fin 9)) :=
    ⋃ i ∈ s, Metric.ball (i : EuclideanSpace ℝ (Fin 9)) (ρ i / 2) with hU
  have hBsubU : B ⊆ U := hs
  have hUopen : IsOpen U := isOpen_biUnion fun i _ => Metric.isOpen_ball
  -- a positive radius below all the chosen radii
  have hδexists : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · refine ⟨(s.image r).min' (hne.image r), ?_, ?_⟩
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ((s.image r).min'_mem (hne.image r))
        rw [← hi]
        exact hr i
      · intro i hi
        exact (s.image r).min'_le (r i) (Finset.mem_image_of_mem r hi)
  obtain ⟨δ, hδpos, hδle⟩ := hδexists
  -- the good property on `U`
  have hgood : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < δ → y ∈ U → ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y) ∈ S := by
    intro t y ht hy k
    rw [hU] at hy
    obtain ⟨i, his, hyi⟩ := Set.mem_iUnion₂.mp hy
    have ht_i : ‖t‖ < r i := lt_of_lt_of_le ht (hδle i his)
    have hy_i : y ∈ Metric.ball (i : EuclideanSpace ℝ (Fin 9)) (ρ i) :=
      Metric.ball_subset_ball (by linarith [hρ i]) hyi
    exact hW i t y ht_i hy_i k
  -- the compact set between the base locus and `U`
  obtain ⟨K, hKc, hKint, hKU⟩ := exists_compact_between hBcomp hUopen hBsubU
  exact ⟨K, δ, hKc, hδpos, fun y hy hm => hKint ⟨hy, hm⟩,
    fun t y ht hy k => hgood t y ht (hKU hy) k⟩

/-! ## 3bis. The pointwise local input (no hypothesis)

The chart-cover remedy for the global Sard is: at each base point `y₀` take the chart centred at its own
value `G 0 0 (bPartC 0 y₀)` and the compact neighbourhood on which the perturbed values stay in that
chart.  That input is *unconditional* — it is `mem_chart_source` plus continuity: -/

/-- **The chart at a base value contains the perturbed values on any prescribed neighbourhood of the
base point.** -/
theorem exists_compact_subset_nhds_of_base_point
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hcont : ∀ k : Fin 3, Continuous
      fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2)
    {y₀ : EuclideanSpace ℝ (Fin 9)} (hm : Work.Drive.TParity.meet3 (G 0) y₀)
    (U : Set (EuclideanSpace ℝ (Fin 9))) (hU : U ∈ 𝓝 y₀) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (ε : ℝ), IsCompact K ∧ 0 < ε ∧ y₀ ∈ interior K ∧
      K ⊆ U ∧
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y)
          ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
              (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source) := by
  classical
  -- the base value is the chart centre, and all three base values equal it
  have hk_eq : ∀ k : Fin 3, G 0 k (Work.Drive.TParity.bPartC k y₀)
      = G 0 0 (Work.Drive.TParity.bPartC 0 y₀) := by
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> tauto
    rcases hk with rfl | rfl | rfl
    · rfl
    · exact hm.1.symm
    · exact hm.2.symm
  -- openness of the joint preimage of the chart source
  have hWopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2)
        ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
            (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source} := by
    rw [show {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
          ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2)
            ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
                (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source}
        = ⋂ k : Fin 3, {q | G q.1 k (Work.Drive.TParity.bPartC k q.2)
            ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
                (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source} from by
      ext q; simp [Set.mem_iInter]]
    refine isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (q.1, Work.Drive.TParity.bPartC k q.2) :=
      continuous_fst.prodMk ((Work.Drive.TParity.bPartC k).continuous.comp continuous_snd)
    exact ((hcont k).comp hc).isOpen_preimage _
      (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
        (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).open_source
  have hbase_mem : ((0 : EuclideanSpace ℝ (Fin m)), y₀)
      ∈ {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
          ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2)
            ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
                (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source} := by
    intro k
    rw [hk_eq k]
    exact mem_chart_source (EuclideanSpace ℝ (Fin 4)) _
  have hW : ({q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      ∀ k : Fin 3, G q.1 k (Work.Drive.TParity.bPartC k q.2)
        ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
            (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source})
        ∈ 𝓝 ((0 : EuclideanSpace ℝ (Fin m)), y₀) := hWopen.mem_nhds hbase_mem
  rw [nhds_prod_eq] at hW
  obtain ⟨U', hU', V, hV, hUV⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU'
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.mem_nhds_iff.mp hU
  set R : ℝ := min (ρ / 2) (r₀ / 2) with hR
  have hRpos : 0 < R := lt_min (half_pos hρ) (half_pos hr₀)
  refine ⟨Metric.closedBall y₀ R, r, isCompact_closedBall y₀ R, hr, ?_, ?_, ?_⟩
  · exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self hRpos)
  · intro x hx
    exact hr₀U (Metric.closedBall_subset_ball
      (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hx)
  · intro t y ht hy k
    have hyρ : y ∈ Metric.ball y₀ ρ :=
      Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hy
    have hyV : y ∈ V := hρV hyρ
    have htU : t ∈ U' := hrU (by rw [Metric.mem_ball, dist_zero_right]; exact ht)
    have hmemUV : ((t, y) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9))
        ∈ U' ×ˢ V := Set.mem_prod.mpr ⟨htU, hyV⟩
    exact hUV hmemUV k

/-- **The chart at a base value contains the perturbed values near that base point.** -/
theorem exists_compact_nhds_of_base_point
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hcont : ∀ k : Fin 3, Continuous
      fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2)
    {y₀ : EuclideanSpace ℝ (Fin 9)} (hm : Work.Drive.TParity.meet3 (G 0) y₀) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (ε : ℝ), IsCompact K ∧ 0 < ε ∧ y₀ ∈ interior K ∧
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y)
          ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _
              (G 0 0 (Work.Drive.TParity.bPartC 0 y₀))).source) := by
  obtain ⟨K, ε, hK, hε, hint, -, hres⟩ :=
    exists_compact_subset_nhds_of_base_point G hcont hm Set.univ (Filter.univ_mem)
  exact ⟨K, ε, hK, hε, hint, hres⟩

/-! ## 4. The single-value discharge -/

/-- **`hloc` is trivial when the base triple locus has one value.**  No knowledge of the chart is
needed: the chart is taken at that value and `mem_chart_source` finishes. -/
theorem hloc_of_single_value
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (p : M)
    (hval : ∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 D y →
      ∀ k : Fin 3, D k (Work.Drive.TParity.bPartC k y) = p) :
    ∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 D y →
      ∀ k : Fin 3, D k (Work.Drive.TParity.bPartC k y)
        ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source := by
  intro y hy hm k
  rw [hval y hy hm k]
  exact mem_chart_source (EuclideanSpace ℝ (Fin 4)) p

/-- **The Sard's chart hypotheses from a single-valued base locus** — the form the design consumes. -/
theorem exists_compact_and_eps_of_single_value
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M)
    (hcont : ∀ k : Fin 3, Continuous
      fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2)
    (hval : ∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 (G 0) y →
      ∀ k : Fin 3, G 0 k (Work.Drive.TParity.bPartC k y) = p) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 9))) (ε : ℝ), IsCompact K ∧ 0 < ε ∧
      (∀ y ∈ Submission.Drive.unitBox 8, Work.Drive.TParity.meet3 (G 0) y → y ∈ interior K) ∧
      (∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y ∈ K →
        ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y)
          ∈ (@chartAt (EuclideanSpace ℝ (Fin 4)) _ M _ _ p).source) :=
  exists_compact_and_eps_of_chartResident G p hcont
    (hloc_of_single_value (G 0) p hval)

/-! ## 5. The `hloc` of the reference triple, for a single-valued base locus -/

section Capping

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **`hloc` of the reference-triple genericity, discharged for a single-valued base locus.**  This is
the exact shape of the hypothesis of `Work.Drive.exists_meet3Hyp_and_goodAt_refTriple`
(`Submission/Work/Drive/refTripleGeneric.lean`). -/
theorem hloc_of_single_value_sweepChartFam
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (p : CappingSpace)
    (hval : ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (Work.Drive.sweepChartFam P Ξ c 0) y →
      ∀ k : Fin 3,
        Work.Drive.sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) = p) :
    ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (Work.Drive.sweepChartFam P Ξ c 0) y →
      ∀ k : Fin 3,
        Work.Drive.sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)
          ∈ (Work.Drive.chr p).source :=
  hloc_of_single_value (Work.Drive.sweepChartFam P Ξ c 0) p hval

/-- The same, with the chart centre taken at a base value: **if the base locus is a single point, then
`hloc` holds for the chart at its value**, with no further input. -/
theorem hloc_of_single_base_point
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (y₀ : EuclideanSpace ℝ (Fin 9))
    (hval : ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (Work.Drive.sweepChartFam P Ξ c 0) y →
      ∀ k : Fin 3,
        Work.Drive.sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)
          = Work.Drive.sweepChartFam P Ξ c 0 0 (Work.Drive.TParity.bPartC 0 y₀)) :
    ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (Work.Drive.sweepChartFam P Ξ c 0) y →
      ∀ k : Fin 3,
        Work.Drive.sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)
          ∈ (Work.Drive.chr (Work.Drive.sweepChartFam P Ξ c 0 0
              (Work.Drive.TParity.bPartC 0 y₀))).source :=
  hloc_of_single_value_sweepChartFam Ξ c _ hval

end Capping

end

end Work.Drive
