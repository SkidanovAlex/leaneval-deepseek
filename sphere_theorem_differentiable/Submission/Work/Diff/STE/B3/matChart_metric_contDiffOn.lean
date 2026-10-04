import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/-- Smoothness of the chart matrix `D.matChart i g₀.inner a b` of the *metric itself* (not of an arbitrary section) on the chart target, in the `g₀`-orthonormal frame `D.e i` of the B3 data.  This is the `h := g₀.inner` instance of the input of `Work.Diff.STE.B3Data.R_contDiff`, and it replaces `Work.Diff.STE.B3.matChart_contDiffOn_of_chartData` there (which needs a `ChartData` hypothesis); here the smoothness of the metric itself is used instead.

ROUTE: copy the proof of `Work.Diff.STE.B3.matChart_contDiffOn_of_chartData` (`Diff/STE/B3/R_contDiff_of_chartData.lean`), replacing its first step (which derives the smoothness of the section of the bundle of bilinear forms from `ChartData`) by the metric's own smoothness: `hsec x := g₀.contMDiff x` (a field of `Submission.Diff.SMet`, i.e. of `ContMDiffRiemannianMetric`), i.e. `ContMDiffAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) ⊤ (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g₀.inner m)) x`.  Then, as there, apply `ContMDiffWithinAt.clm_bundle_apply₂` with the two frame fields (`D.hesm i a`, `D.hesm i b`, which are globally smooth by `B3Data.hesm`), take the second component (`contMDiffWithinAt_totalSpace`), and compose with `(extChartAt I (D.x₀ i)).symm` via `contMDiffOn_extChartAt_symm`.  No `[T2Space M]` is needed anywhere here (`clm_bundle_apply₂` and `contMDiffOn_extChartAt_symm` are `T2Space`-free). -/
theorem matChart_metric_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i g₀.inner a b) (extChartAt I (D.x₀ i)).target := by
  -- The metric `g₀`, viewed as a section of the bundle of bilinear forms, is smooth at every
  -- point: this is the `contMDiff` field of the `ContMDiffRiemannianMetric` structure.
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g₀.inner x)) x :=
    fun x => g₀.contMDiff x
  -- ... hence its matrix in the globally smooth frame `D.e i` is smooth everywhere
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => g₀.inner x (D.e i a x) (D.e i b x)) univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  -- read that matrix in the chart coordinate of the chart at `D.x₀ i`
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => g₀.inner ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => mem_univ _)
  exact hcomp.contDiffOn

end Work.Diff.STE.B3
