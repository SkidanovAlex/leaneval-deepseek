import Mathlib
import Submission.Work.Diff.STE.exists_chart_ball_cover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A finite cover of a compact manifold by coordinate balls, with a subordinate smooth partition of
unity

Layer B (`B1`) of the STE design: on a compact (`T2`, boundaryless) manifold there is a finite
family of points `x₀ i` and positive radii `r i` such that

* the closed coordinate balls `closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)` are contained in the
  chart targets `(extChartAt I (x₀ i)).target`,
* the corresponding open coordinate balls cover `M`,
* and a smooth partition of unity `θ` is subordinate to that cover.

The cover without the partition of unity is `Work.Diff.STE.exists_chart_ball_cover`; the partition
of unity comes from Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`.

The one subtle point: the sets `(extChartAt I x) ⁻¹' ball …` occurring in the statement are **not**
known to be open (only their intersections with the chart source are, see
`isOpen_extChartAt_preimage`).  So one first produces the finite cover by the smaller *open* family
`(chartAt H x).source ∩ (extChartAt I x) ⁻¹' ball …`, applies `exists_isSubordinate` there, and then
weakens both the cover statement and the subordination along `source ∩ · ⊆ ·`.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

/-- **Finite cover by open coordinate balls contained in the chart targets.**

Same as `exists_chart_ball_cover`, but the covering sets are the (genuinely open) sets
`(chartAt H x).source ∩ (extChartAt I x) ⁻¹' ball ((extChartAt I x) x) r`. -/
theorem exists_chart_ball_cover_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    [I.Boundaryless] :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (x₀ : ι₀ → M) (r : ι₀ → ℝ),
      (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)
        ⊆ (extChartAt I (x₀ i)).target) ∧
      (⋃ i, (chartAt H (x₀ i)).source ∩ (extChartAt I (x₀ i)) ⁻¹'
        Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)) = Set.univ := by
  classical
  -- Step 1: at every point a positive radius whose coordinate closed ball stays in the target.
  have hrad : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((extChartAt I x) x) ρ ⊆ (extChartAt I x).target := by
    intro x
    have hmem : (extChartAt I x) x ∈ (extChartAt I x).target := mem_extChartAt_target x
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target x).mem_nhds hmem)
    exact ⟨ε / 2, by linarith,
      fun y hy => hsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  choose r hrpos hrsub using hrad
  -- Step 2: the chart balls (intersected with the chart sources) form an open cover of `M`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt H x).source ∩
      (extChartAt I x) ⁻¹' Metric.ball ((extChartAt I x) x) (r x))
    (fun x => isOpen_extChartAt_preimage x Metric.isOpen_ball)
    (fun y _ => Set.mem_iUnion.mpr
      ⟨y, mem_chart_source H y, Metric.mem_ball_self (hrpos y)⟩)
  -- Step 3: enumerate the finite subcover by `Fin t.card`.
  let x₀ : Fin t.card → M := fun i => ((t.equivFin.symm i : {x // x ∈ t}) : M)
  let r₀ : Fin t.card → ℝ := fun i => r (x₀ i)
  refine ⟨Fin t.card, inferInstance, x₀, r₀, ?_, ?_, ?_⟩
  · intro i
    exact hrpos _
  · intro i
    exact hrsub _
  · refine Set.eq_univ_iff_forall.mpr (fun y => ?_)
    show y ∈ ⋃ i, (chartAt H (x₀ i)).source ∩ (extChartAt I (x₀ i)) ⁻¹'
      Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r₀ i)
    rw [Set.mem_iUnion]
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    have hxx : x₀ (t.equivFin ⟨x, hx⟩) = x := by
      simp only [x₀]
      rw [Equiv.symm_apply_apply]
    simpa only [r₀, hxx] using hxy

/-- **Smooth partition of unity subordinate to a finite cover by coordinate balls.**

On a compact boundaryless smooth manifold there is a finite family of points `x₀ i` and positive
radii `r i` such that the closed coordinate balls `closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)`
lie in the chart targets `(extChartAt I (x₀ i)).target`, the corresponding open coordinate balls
cover `M`, and a smooth partition of unity `θ` is subordinate to that cover. -/
theorem exists_smoothPartition_ball_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [CompactSpace M] [T2Space M] [I.Boundaryless] :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (x₀ : ι₀ → M) (r : ι₀ → ℝ)
      (θ : SmoothPartitionOfUnity ι₀ I M),
      (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)
        ⊆ (extChartAt I (x₀ i)).target) ∧
      (⋃ i, (extChartAt I (x₀ i)) ⁻¹'
        Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)) = Set.univ ∧
      θ.IsSubordinate (fun i : ι₀ => (extChartAt I (x₀ i)) ⁻¹'
        Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)) := by
  classical
  -- Step 1: the finite cover by *open* coordinate balls.
  obtain ⟨ι₀, hfin, x₀, r, hrpos, hrsub, hcov⟩ :=
    exists_chart_ball_cover_open (I := I) (M := M)
  -- Step 2: a smooth partition of unity subordinate to that open cover.
  -- (`M` is compact, hence σ-compact and Hausdorff, so Mathlib's existence theorem applies.)
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun i : ι₀ => (chartAt H (x₀ i)).source ∩ (extChartAt I (x₀ i)) ⁻¹'
      Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i))
    (fun i => isOpen_extChartAt_preimage (x₀ i) Metric.isOpen_ball)
    hcov.symm.le
  refine ⟨ι₀, hfin, x₀, r, θ, hrpos, hrsub, ?_, ?_⟩
  · -- The coordinate balls (without the chart-source intersection) still cover `M`.
    refine Set.eq_univ_iff_forall.mpr (fun y => ?_)
    have hy : y ∈ ⋃ i : ι₀, (chartAt H (x₀ i)).source ∩ (extChartAt I (x₀ i)) ⁻¹'
        Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i) := by
      rw [hcov]
      exact Set.mem_univ y
    rw [Set.mem_iUnion] at hy ⊢
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, hi.2⟩
  · -- Subordination is weakened along `source ∩ · ⊆ ·`.
    intro i
    exact (hθ i).trans Set.inter_subset_right

end Work.Diff.STE
