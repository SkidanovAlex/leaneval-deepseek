import Mathlib
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior
import Submission.Work.EXT.exists_smooth_ONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart matrix of a smooth metric is smooth at every interior point of the chart target.**

This is the `interior`-form of `Work.Diff.EXT.kz_contDiffAt_chartMatFun` (which asks for the
hypotheses `[I.Boundaryless]` and `[T2Space M]` that we cannot afford here).  The ingredients are:
the chart inverse is smooth *on the interior* of the target (an open set), `PartialEquiv.map_target`
identifies the corresponding point of `M`, and `Work.EXT.ONF.pairing` is the T2-free version of the
metric-pairing smoothness lemma. -/
lemma chartMatFun_contDiffAt_of_mem_interior (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ interior ((extChartAt I x₀).target)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g x₀) y := by
  have hyt : y ∈ (extChartAt I x₀).target := interior_subset hy
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hyt
  have hsymm : ContMDiffAt (modelWithCornersSelf ℝ E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt I I.tangent ∞
        (fun z : M => TotalSpace.mk' E z
          (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) k)))
        ((extChartAt I x₀).symm y) :=
    fun k => Work.Diff.EXT.contMDiffAt_frameVector x₀ (Work.Diff.EXT.bB (E := E) k) hp
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  have hpair : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) j)))
      ((extChartAt I x₀).symm y) :=
    Work.EXT.ONF.pairing g ((extChartAt I x₀).symm y) (hframe i) (hframe j)
  have hcomp : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : E => g.inner ((extChartAt I x₀).symm x)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x)
          (Work.Diff.EXT.bB (E := E) j))) y :=
    hpair.comp y hsymm
  have h := contMDiffAt_iff_contDiffAt.mp hcomp
  simpa only [Work.Diff.EXT.chartMatFun] using h

theorem dens_interior_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
      interior ((extChartAt I (D.x₀ i)).target)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i) z := by
  have hflat : ContDiffAt ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i)) z :=
    (contDiff_flatToE (I := I) (M := M) (D.x₀ i)).contDiffAt
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞)
      (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i))
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) :=
    chartMatFun_contDiffAt_of_mem_interior (I := I) (M := M) g₀ (D.x₀ i) hz
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) z :=
    hchart.comp z hflat
  have hdet : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))).det) z :=
    (Work.Diff.STE.B3.contDiff_det_of (n := Module.finrank ℝ E)).contDiffAt.comp z hcomp
  have hy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z
      ∈ (extChartAt I (D.x₀ i)).target := interior_subset hz
  have hsrc : (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
      ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i)]
    exact PartialEquiv.map_target (extChartAt I (D.x₀ i)) hy
  have hpos : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))).det := by
    have := (Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hsrc).det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) from rfl] at this
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Real.sqrt ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))).det)) z :=
    (Real.contDiffAt_sqrt hpos.ne').comp z hdet
  show ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Real.sqrt (Matrix.det (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))))) z
  exact hsqrt

end Work.Diff.STE.D
