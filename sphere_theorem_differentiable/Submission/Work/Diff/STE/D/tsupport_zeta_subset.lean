import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The *topological* support of the Layer B3 weights sits in the chart source

`B3Data.hζsupp` gives, for every point `p` of the (ordinary) support of `ζ i`,
`p ∈ (extChartAt I (x₀ i)).source` and `‖coord (x₀ i) p‖ < σ i`.  The chart source is *open*,
so this alone does not control the *topological* support `tsupport (ζ i) = closure (support (ζ i))`
— the closure could in principle run out of the source.  What saves the statement is the *quantitative*
part of the hypothesis together with `B3Data.htarget`:

* the closed `2 σ i`-coordinate ball lies in the target of the chart at `x₀ i` (`htarget`), hence
  its image under `pt i = (extChartAt I (x₀ i)).symm ∘ flatToE` lies in the chart *source*
  (`PartialEquiv.map_target`);
* `pt i` is continuous on the closed `2 σ i`-ball (`continuousAt_extChartAt_symm''`, which is
  unconditional on the target), so the image of the closed `σ i`-ball — an honest compact subset of
  `E`, with the chart centre in its interior — is compact, hence closed in the Hausdorff space `M`;
* every point of the support of `ζ i` lies in that compact set, since there `p = pt i (coord p)`
  (`pt_coord`) and `‖coord p‖ < σ i`.

The topological support, being the closure of a set contained in a closed set, is therefore
contained in the chart source.
-/

namespace Work.Diff.STE.D

theorem tsupport_zeta_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    tsupport (D.ζ i) ⊆ (extChartAt I (D.x₀ i)).source := by
  intro p hp
  -- `flatToE` is an affine map, hence continuous.
  have hflat : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) := by
    have h1 : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z :=
      continuous_const.add continuous_id
    have h2 : Continuous fun w : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun.symm w :=
      (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E).toContinuousLinearMap).continuous
    exact h2.comp h1
  -- `pt i` is continuous on the closed `2σ i`-ball, because there the chart at `x₀ i` is genuine.
  have hcont : ContinuousOn (fun z : Fin (Module.finrank ℝ E) → ℝ => D.pt i z)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)) := by
    intro z hz
    have hz2 : ‖z‖ ≤ 2 * D.σ i := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    have hpt : ContinuousAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) z :=
      ((continuousAt_extChartAt_symm'' (I := I) (D.htarget i z hz2)).comp hflat.continuousAt)
    exact hpt.continuousWithinAt
  -- the compact set of flat coordinates.
  have hcompact : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) :=
    isCompact_closedBall _ _
  -- its `pt i`-image lies in the chart source.
  have himage : D.pt i '' Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)
      ⊆ (extChartAt I (D.x₀ i)).source := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ ≤ D.σ i := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact (extChartAt I (D.x₀ i)).map_target (D.htarget i z (by linarith [D.hσ i]))
  -- hence it is closed (it is the continuous image of a compact set, in a Hausdorff space).
  have hKclosed : IsClosed (D.pt i '' Metric.closedBall
      (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) :=
    (hcompact.image_of_continuousOn
      (hcont.mono (Metric.closedBall_subset_closedBall (by linarith [D.hσ i])))).isClosed
  -- the support of `ζ i` is contained in that image.
  have hsupp : Function.support (D.ζ i) ⊆
      D.pt i '' Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
    intro q hq
    obtain ⟨hsrc, hlt⟩ := D.hζsupp i q hq
    refine ⟨Work.Diff.STE.coord (I := I) (D.x₀ i) q, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using le_of_lt hlt
    · exact D.pt_coord i hsrc
  have hcl : closure (Function.support (D.ζ i)) ⊆ (extChartAt I (D.x₀ i)).source :=
    (hKclosed.closure_subset_iff.mpr hsupp).trans himage
  exact hcl (by simpa only [tsupport] using hp)

end Work.Diff.STE.D
