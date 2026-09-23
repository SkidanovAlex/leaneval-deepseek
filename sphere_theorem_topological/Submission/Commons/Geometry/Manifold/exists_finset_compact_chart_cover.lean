import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Order.CompletePartialOrder

namespace Commons.Geometry.Manifold

open Set

set_option linter.style.haveILetI false

/-- Around each point of a boundaryless charted space there is an open neighbourhood whose
closure is compact and contained in the source of the chart at that point. -/
private lemma exists_compact_closure_nhds_subset_chartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [I.Boundaryless] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (chartAt H x).source := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I) x)
  have hε2 : 0 < ε / 2 := by linarith
  have hballsub : Metric.closedBall (extChartAt I x x) (ε / 2) ⊆ (extChartAt I x).target :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεball
  set U : Set M :=
    (chartAt H x).source ∩ (extChartAt I x) ⁻¹' Metric.ball (extChartAt I x x) (ε / 2)
    with hUdef
  have hUopen : IsOpen U := isOpen_extChartAt_preimage x Metric.isOpen_ball
  have hxU : x ∈ U := ⟨mem_chart_source H x, Metric.mem_ball_self hε2⟩
  set K : Set M :=
    (extChartAt I x).symm '' Metric.closedBall (extChartAt I x x) (ε / 2) with hKdef
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm x).mono hballsub)
  have hKsource : K ⊆ (chartAt H x).source := by
    rw [hKdef]
    rintro z ⟨y, hy, rfl⟩
    simpa only [extChartAt_source] using (extChartAt I x).map_target (hballsub hy)
  have hUK : U ⊆ K := by
    intro z hz
    obtain ⟨hzs, hzb⟩ := hz
    have hzs' : z ∈ (extChartAt I x).source := by simpa only [extChartAt_source] using hzs
    rw [hKdef]
    exact ⟨extChartAt I x z, Metric.ball_subset_closedBall hzb,
      (extChartAt I x).left_inv hzs'⟩
  have hclK : closure U ⊆ K := closure_minimal hUK hKcompact.isClosed
  exact ⟨U, hUopen, hxU,
    hKcompact.of_isClosed_subset isClosed_closure hclK, hclK.trans hKsource⟩

theorem exists_finset_compact_chart_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M]
    [I.Boundaryless] [CompactSpace M] [Nonempty M] :
    ∃ (S : Finset M) (Z : M → Set M),
      S.Nonempty ∧ (∀ z ∈ S, IsCompact (Z z)) ∧ (∀ z ∈ S, (Z z).Nonempty) ∧
      (∀ z ∈ S, z ∈ Z z) ∧ (∀ z ∈ S, Z z ⊆ (chartAt H z).source) ∧
      (⋃ z ∈ (S : Set M), Z z) = Set.univ := by
  choose U hU using fun x : M => exists_compact_closure_nhds_subset_chartAt (I := I) x
  have hUo : ∀ x, IsOpen (U x) := fun x => (hU x).1
  have hxU : ∀ x, x ∈ U x := fun x => (hU x).2.1
  have hUcomp : ∀ x, IsCompact (closure (U x)) := fun x => (hU x).2.2.1
  have hUsrc : ∀ x, closure (U x) ⊆ (chartAt H x).source := fun x => (hU x).2.2.2
  have hcover : (univ : Set M) ⊆ ⋃ x, U x :=
    fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hcover
  have hUnionU : (⋃ i ∈ (S : Set M), U i) = univ := by
    apply subset_antisymm (subset_univ _)
    intro m hm
    simpa only [Finset.mem_coe] using hS hm
  refine ⟨S, fun z => closure (U z), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨m⟩ := ‹Nonempty M›
    have hm : m ∈ ⋃ i ∈ S, U i := hS (mem_univ m)
    rw [mem_iUnion] at hm
    obtain ⟨i, hi⟩ := hm
    rw [mem_iUnion] at hi
    exact ⟨i, hi.1⟩
  · exact fun z _ => hUcomp z
  · exact fun z _ => ⟨z, subset_closure (hxU z)⟩
  · exact fun z _ => subset_closure (hxU z)
  · exact fun z _ => hUsrc z
  · apply subset_antisymm (subset_univ _)
    intro m hm
    rw [← hUnionU] at hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    obtain ⟨hiS, himU⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiS, subset_closure himU⟩⟩

end Commons.Geometry.Manifold