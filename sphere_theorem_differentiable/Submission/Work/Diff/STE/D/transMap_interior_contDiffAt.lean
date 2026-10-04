import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

theorem transMap_interior_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈
      interior ((extChartAt I (D.x₀ j)).target))
    (hz2 : D.pt j z ∈ (extChartAt I (D.x₀ i)).source) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z := by
  -- `z ↦ pt j z` is smooth at `z`: `flatToE (x₀ j)` is affine and `(extChartAt I (x₀ j))⁻¹` is
  -- smooth on the *interior* of the chart target (which is open also in the boundary case).
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior D j z hz1
  -- The chart `extChartAt I (x₀ i)` is smooth at `pt j z`, since that point lies in its source
  -- (and `(extChartAt I x).source = (chartAt H x).source`).
  have hsrc : D.pt j z ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source I (D.x₀ i)]
    exact hz2
  have hcomp := (contMDiffAt_extChartAt' (I := I) (x := D.x₀ i) hsrc).comp z hpt
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (extChartAt I (D.x₀ i)) (D.pt j w)) z :=
    contMDiffAt_iff_contDiffAt.mp hcomp
  -- `finBasis.equivFun` is linear, hence smooth.
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => (Module.finBasis ℝ E).equivFun y) :=
    (((Module.finBasis ℝ E).equivFun : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) :
      E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).toContinuousLinearMap.contDiff
  have h5 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.pt j w))) z :=
    hlin.contDiffAt.comp z h4
  have h6 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.pt j w))
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))) z :=
    h5.sub contDiffAt_const
  simpa only [Work.Diff.STE.coord] using h6

end Work.Diff.STE.D
