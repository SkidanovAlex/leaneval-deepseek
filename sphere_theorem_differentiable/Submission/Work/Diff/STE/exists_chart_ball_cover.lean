import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- **Finite cover by coordinate balls contained in the chart target.**

On a compact charted space (with boundaryless model), there is a finite family of points `x₀ i`
and positive radii `r i` such that the closed coordinate balls
`closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)` of the extended charts lie inside the chart
targets `(extChartAt I (x₀ i)).target`, and such that the corresponding open balls already cover
`M`. -/
theorem exists_chart_ball_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    [I.Boundaryless] :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (x₀ : ι₀ → M) (r : ι₀ → ℝ),
      (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)
        ⊆ (extChartAt I (x₀ i)).target) ∧
      (⋃ i, (extChartAt I (x₀ i)) ⁻¹'
        Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)) = Set.univ := by
  classical
  -- Step 1: at every point, a positive radius whose coordinate closed ball stays in the target.
  have hrad : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((extChartAt I x) x) ρ ⊆ (extChartAt I x).target := by
    intro x
    have hmem : (extChartAt I x) x ∈ (extChartAt I x).target := mem_extChartAt_target x
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target x).mem_nhds hmem)
    exact ⟨ε / 2, by linarith,
      fun y hy => hsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  choose r hrpos hrsub using hrad
  -- Step 2: the corresponding chart balls form an open cover of the compact space.
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
    show 0 < r (x₀ i)
    exact hrpos _
  · intro i
    show Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r (x₀ i)) ⊆
      (extChartAt I (x₀ i)).target
    exact hrsub _
  · refine Set.eq_univ_iff_forall.mpr (fun y => ?_)
    show y ∈ ⋃ i, (extChartAt I (x₀ i)) ⁻¹'
      Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r (x₀ i))
    rw [Set.mem_iUnion]
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    have hxx : x₀ (t.equivFin ⟨x, hx⟩) = x := by
      simp only [x₀]
      rw [Equiv.symm_apply_apply]
    simpa only [Set.mem_preimage, hxx] using hyx.2

end Work.Diff.STE
