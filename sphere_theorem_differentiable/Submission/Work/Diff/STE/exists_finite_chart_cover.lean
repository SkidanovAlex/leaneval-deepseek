import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- On a compact charted space, finitely many charts (taken at finitely many points of `M`)
already cover `M`.  Note that the index type `ι₀` is required to live in `Type 0`, so we
enumerate the finite set of centres by `Fin t.card` via `Finset.equivFin`. -/
theorem exists_finite_chart_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (x : ι₀ → M),
      (⋃ i, (chartAt H (x i)).source) = Set.univ := by
  classical
  -- The charts at all points of `M` form an open cover, since each point lies in its own chart.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, mem_chart_source H y⟩)
  -- Enumerate the finite set `t` by `Fin t.card` (a type in `Type 0`).
  refine ⟨Fin t.card, inferInstance, (fun i => ((t.equivFin.symm i : {x // x ∈ t}) : M)), ?_⟩
  refine Set.eq_univ_iff_forall.mpr (fun y => ?_)
  rw [Set.mem_iUnion]
  have hy := ht (Set.mem_univ y)
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hyx⟩ := hy
  refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  have h : (t.equivFin.symm (t.equivFin ⟨x, hx⟩) : {x // x ∈ t}) = ⟨x, hx⟩ :=
    Equiv.symm_apply_apply _ _
  simpa [h] using hyx

end Work.Diff.STE
