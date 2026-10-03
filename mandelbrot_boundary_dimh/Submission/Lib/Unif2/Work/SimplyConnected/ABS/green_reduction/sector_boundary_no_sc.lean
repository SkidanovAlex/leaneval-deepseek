import Submission.Lib.Unif2.Work.SimplyConnected.ABS.region_with_sector_boundary

/-!
# The sector condition from a one-sided local level set, without `SimplyConnectedSpace`

`Work.SimplyConnected.ABS.hasSectorBoundary_of_local_sublevel` (in
`region_with_sector_boundary.lean`) carries a `[SimplyConnectedSpace X]` section variable that its
statement and proof do not use.  The deliverable
`Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region` works in a
context **without** that instance, so the lemma is restated here (with the same proof: the only
non-trivial ingredient is `exists_wedge_of_hasFDerivAt`, which is a statement about `ℂ` alone).
-/

open Set Metric Filter
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Work.SimplyConnected.ABS.green_reduction

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The sector condition from a local one-sided sub-level description**, without the spurious
`SimplyConnectedSpace` hypothesis. -/
theorem hasSectorBoundary_of_local_sublevel' {W : Set X} {p : X} {u : X → ℝ}
    {L : ℂ →L[ℝ] ℝ}
    (hderiv : HasFDerivAt (fun z : ℂ => u ((chartAt ℂ p).symm z)) L ((chartAt ℂ p) p))
    (hL : L ≠ 0)
    (hside : ∀ᶠ y in 𝓝 p, y ∈ W → ¬ (u p < u y)) :
    Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  classical
  obtain ⟨L1, L2, hL1, hL2, hwit, r, hr, hwedge⟩ :=
    Work.SimplyConnected.ABS.exists_wedge_of_hasFDerivAt
      (phi := fun z : ℂ => u ((chartAt ℂ p).symm z)) hL hderiv
  rcases Filter.eventually_iff_exists_mem.mp hside with ⟨V, hVmem, hVside⟩
  set V0 : Set X := (interior V ∩ (chartAt ℂ p).source) ∩
      ((chartAt ℂ p).source ∩ (chartAt ℂ p) ⁻¹' Metric.ball ((chartAt ℂ p) p) r)
    with hV0
  have hV0open : IsOpen V0 := by
    rw [hV0]
    exact (isOpen_interior.inter (chartAt ℂ p).open_source).inter
      (ContinuousOn.isOpen_inter_preimage (chartAt ℂ p).continuousOn_toFun
        (chartAt ℂ p).open_source Metric.isOpen_ball)
  have hpV0 : p ∈ V0 := by
    rw [hV0]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hVmem, mem_chart_source ℂ p⟩,
      mem_chart_source ℂ p, Metric.mem_ball_self hr⟩
  have hV0sub : V0 ⊆ (chartAt ℂ p).source := by
    rw [hV0]; exact fun x hx => hx.1.2
  refine ⟨chartAt ℂ p, V0, L1, L2, chart_mem_atlas ℂ p, hV0open, hpV0, hV0sub,
    mem_chart_source ℂ p, hL1, hL2, hwit, ?_⟩
  rintro x ⟨hxW, hxV⟩ ⟨h1, h2⟩
  have hxsrc : x ∈ (chartAt ℂ p).source := hxV.1.2
  have hxball : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r := hxV.2.2
  have hdist : dist ((chartAt ℂ p) x) ((chartAt ℂ p) p) < r := hxball
  have hlt : u ((chartAt ℂ p).symm ((chartAt ℂ p) p))
      < u ((chartAt ℂ p).symm ((chartAt ℂ p) x)) :=
    hwedge ((chartAt ℂ p) x) hdist ⟨h1, h2⟩
  rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p),
    (chartAt ℂ p).left_inv hxsrc] at hlt
  have := hVside x (interior_subset hxV.1.1) hxW
  linarith

end Work.SimplyConnected.ABS.green_reduction
