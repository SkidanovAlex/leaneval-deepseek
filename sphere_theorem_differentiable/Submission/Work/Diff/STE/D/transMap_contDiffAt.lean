import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.D.interior_of_flatBall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `flatToE x₀` is smooth (it is affine).  Copy of `Work.Diff.STE.contDiff_flatToE` without the
unused `[I.Boundaryless]` hypothesis of that lemma. -/
lemma contDiff_flatToE' (x₀ : M) : ContDiff ℝ (⊤ : ℕ∞) (flatToE (I := I) x₀) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) :=
    contDiff_const.add contDiff_id
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun.symm w) :=
    (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) :
        (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap.contDiff
  exact h2.comp h1

end Aux

/-- **The chart transition `z ↦ coord (x₀ i) (pt j z)` is smooth where both charts are genuine.**

Here `pt j z = (extChartAt I (x₀ j)).symm (flatToE (x₀ j) z)` and
`coord (x₀ i) p = equivFun ((extChartAt I (x₀ i)) p) - equivFun ((extChartAt I (x₀ i)) (x₀ i))`.

Assumptions: the flat coordinate `z` is in the target of the chart at `x₀ j` (so `pt j` is genuine
near `z`) and `pt j z` is in the source of the chart at `x₀ i` (so `coord (x₀ i)` is genuine there).

Suggested route: `coord (x₀ i) (pt j ·)` is the composite of the affine map `flatToE (x₀ j)` with
`(extChartAt I (x₀ j)).symm` (smooth on the target, `contMDiffOn_extChartAt_symm` /
`B3Data.contMDiffAt_pt` in `Diff/STE/B3/CompSmooth`), then with `extChartAt I (x₀ i)`
(smooth on its source, `contMDiffAt_extChartAt'`), then with the linear equivalence `finBasis` and
a translation. -/
theorem transMap_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hz2 : D.pt j z ∈ (extChartAt I (D.x₀ i)).source) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z := by
  classical
  -- the manifold is at least `C¹` (needed for the chart-independence of interior points)
  haveI hM1 : IsManifold I 1 M :=
    IsManifold.of_le (m := 1) (n := ((⊤ : ENat) : WithTop ENat)) (by simp)
  -- ## Step 1: the flat coordinate of `pt j z` in the chart at `x₀ j` is `z` itself
  have hxb_j : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target hz1
  have hyval : (extChartAt I (D.x₀ j)) (D.pt j z) = Work.Diff.STE.flatToE (I := I) (D.x₀ j) z :=
    (extChartAt I (D.x₀ j)).right_inv hz1
  have hxb_j_chart : D.pt j z ∈ (chartAt H (D.x₀ j)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ j)]; exact hxb_j
  have hxb_i_chart : D.pt j z ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i)]; exact hz2
  -- ## Step 2: `hcover` supplies a chart whose flat `σ`-ball contains the point
  obtain ⟨i', hsrc'_i, hcoord'_i⟩ := D.hcover (D.pt j z)
  have hsrc'_i_chart : D.pt j z ∈ (chartAt H (D.x₀ i')).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i')]; exact hsrc'_i
  -- ## Step 3: in that chart the chart value of the point is an interior point of `range I`
  have hint_i : (extChartAt I (D.x₀ i')) (D.pt j z) ∈ interior (Set.range I) :=
    Work.Diff.STE.D.interior_of_flatBall (I := I) (D.x₀ i') (D.σ i') (D.hσ i') (D.pt j z)
      (fun z' hz' => D.htarget i' z' hz') hcoord'_i
  -- ## Step 4: chart-independence of interior points: the same holds in the chart at `x₀ j`
  have htarget_j : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈
      interior ((extChartAt I (D.x₀ j)).target) := by
    have hei : ((chartAt H (D.x₀ i')).extend I) (D.pt j z) ∈
        interior (((chartAt H (D.x₀ i')).extend I)).target :=
      (chartAt H (D.x₀ i')).mem_interior_extend_target
        ((chartAt H (D.x₀ i')).map_source hsrc'_i_chart) hint_i
    have hiff := ModelWithCorners.mem_interior_range_iff_of_mem_atlas (I := I) (M := M)
      (n := 1) (e := chartAt H (D.x₀ i')) (e' := chartAt H (D.x₀ j)) (x := D.pt j z)
      one_ne_zero (chart_mem_atlas H _) (chart_mem_atlas H _) hsrc'_i_chart hxb_j_chart
    have hmem := (hiff.mp hei : ((chartAt H (D.x₀ j)).extend I) (D.pt j z) ∈
      interior (((chartAt H (D.x₀ j)).extend I)).target)
    rw [← hyval]
    exact hmem
  -- ## Step 5: hence the chart target is a neighbourhood of the flat coordinate
  have hnhds : (extChartAt I (D.x₀ j)).target ∈
      𝓝 (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) :=
    mem_of_superset ((isOpen_interior).mem_nhds htarget_j) interior_subset
  -- ## Step 6: `pt j` is smooth at `z`
  have hflatdiff : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j)) z :=
    contMDiffAt_iff_contDiffAt.mpr ((contDiff_flatToE' (I := I) (D.x₀ j)).contDiffAt)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (⊤ : ℕ∞) ((extChartAt I (D.x₀ j)).symm)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) :=
    ((contMDiffOn_extChartAt_symm (I := I) (n := (⊤ : ℕ∞)) (D.x₀ j)).mono interior_subset).contMDiffAt
      ((isOpen_interior).mem_nhds htarget_j)
  have hpt : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I (⊤ : ℕ∞) (D.pt j) z :=
    hsymm.comp z hflatdiff
  -- ## Step 7: `coord (x₀ i)` is a smooth function of the point
  have hchart_i : ContMDiffAt I 𝓘(ℝ, E) (⊤ : ℕ∞) (extChartAt I (D.x₀ i)) (D.pt j z) :=
    contMDiffAt_extChartAt' (I := I) (x := D.x₀ i) hxb_i_chart
  have hcoord : ContMDiffAt I 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) (⊤ : ℕ∞)
      (fun p : M => Work.Diff.STE.coord (I := I) (D.x₀ i) p) (D.pt j z) := by
    set L : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
      (((Module.finBasis ℝ E).equivFun : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) :
        E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).toContinuousLinearMap with hLdef
    have hLapp : ∀ v : E, (Module.finBasis ℝ E).equivFun v = L v := fun v => rfl
    set c : Fin (Module.finrank ℝ E) → ℝ :=
      (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) with hcdef
    have haff : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) (⊤ : ℕ∞)
        (fun v : E => L v - c) ((extChartAt I (D.x₀ i)) (D.pt j z)) :=
      contMDiffAt_iff_contDiffAt.mpr ((L.contDiff.sub contDiff_const).contDiffAt)
    have hcomp := haff.comp (D.pt j z) hchart_i
    have hfun : (fun p : M => Work.Diff.STE.coord (I := I) (D.x₀ i) p)
        = fun p : M => L ((extChartAt I (D.x₀ i)) p) - c := by
      funext p
      simp only [Work.Diff.STE.coord, hLapp, hcdef]
    rw [hfun]
    exact hcomp
  -- ## Step 8: assemble and convert to `ContDiffAt`
  have hfinal : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) (⊤ : ℕ∞)
      (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z :=
    hcoord.comp z hpt
  exact contMDiffAt_iff_contDiffAt.mp hfinal

/-! ## Proof note

Why `hz1` is enough, although the target of an extended chart need not be open in the model space
when `I` has a boundary.  Write `x_b := pt j z`.  By `D.hcover` there is a chart centre `x₀ i'`
with `x_b` in its source and flat coordinate of norm `≤ D.σ i'`; combined with `D.htarget i'` (the
flat `2σ i'`-ball maps into the chart target) this shows that the chart value of `x_b` in the chart
at `x₀ i'` is an *interior* point of `Set.range I` (that is exactly
`Work.Diff.STE.D.interior_of_flatBall`, delegated to `Diff/STE/D/interior_of_flatBall.lean`).
Since the notion of interior point is independent of the chart
(`ModelWithCorners.mem_interior_range_iff_of_mem_atlas`), the chart value of `x_b` in the chart at
`x₀ j`, i.e. `flatToE (x₀ j) z` itself, lies in the interior of the target of that chart — hence
that target is a neighbourhood of `flatToE (x₀ j) z`, and `(extChartAt I (x₀ j)).symm` is genuinely
smooth there.  Without the insertion of the chart `x₀ i'` (and of the chart-independence of the
notion of interior) the claim is *false* for a model with boundary. -/

end Work.Diff.STE.D
