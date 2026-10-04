/-
# Smoothness of the metric, reconstructed from its chart matrix

`Work.Diff.EXT.chartMat G x₀ t y` is the matrix of the metric `G t` in the coordinate frame of the
chart at `x₀`, as a function of the chart coordinate `y` (`Submission/Work/Diff/EXT/splice_defs.lean`),
and `Work.Diff.EXT.matToBilin` (`Submission/Work/Diff/EXT/bilinMat.lean`) is the linear
reconstruction of a bilinear form from its matrix in the basis `bB`.

This file proves the geometric face of that reconstruction: if the chart matrix of a family of
metrics is `C^∞` as a function of `(t, y)` (a hypothesis that `JointSmooth` supplies upstream),
then the assembled bilinear form

`(t, x) ↦ matToBilin (fun i j => chartMat G x₀ t ((extChartAt I x₀) x) i j)`

is `C^∞` as a function on the manifold `ℝ × M` at `(t₀, x₀)`.  This is the smoothness of the metric
as a section of the bundle of bilinear forms, and it is the input that
`Work.Diff.EXT.contMDiffAt_section_of_chartMat` uses to compute the splice.

The proof is the obvious one, in two steps:

* `(t, x) ↦ (t, (extChartAt I x₀) x)` is `C^∞` at `(t₀, x₀)` (product test, `comp_of_eq`), and
* `matToBilin` is linear and continuous, hence `C^∞`, so its composition with the above is `C^∞`.

Both steps are pure `ContMDiffAt`/`ContDiffAt` bookkeeping.  The only technicality is that
synthesising the algebraic structure of the continuous-linear-map space
`E →L[ℝ] E →L[ℝ] ℝ` is expensive, so `synthInstance.maxHeartbeats` is raised here (as in
`bilinMat.lean`), and that `ContinuousLinearMap.contDiff` has to be applied with the domain and
codomain of the map written out explicitly, since the continuous-linear-map structure on the
Pi type `MatE` is elaborated with its own (definitionally equal, but not syntactically identical)
instances.
-/

import Mathlib
import Submission.Work.Diff.EXT.bilinMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.Diff.EXT

theorem contMDiffAt_matToBilin_chartMat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (h : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (t₀, (extChartAt I x₀) x₀)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.matToBilin
        (fun i j => Work.Diff.EXT.chartMat G x₀ p.1 ((extChartAt I x₀) p.2) i j))
      (t₀, x₀) := by
  -- Step 1: the coordinate map `(t, x) ↦ (t, chart x)` is smooth.
  have hf : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (𝓘(ℝ, ℝ × E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) (t₀, x₀) := by
    refine (contMDiffAt_prod_module_iff (I := (modelWithCornersSelf ℝ ℝ).prod I)
      (f := fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2))).mpr ⟨?_, ?_⟩
    · exact contMDiffAt_fst
    · have h1 : ContMDiffAt I 𝓘(ℝ, E) (⊤ : ℕ∞) (extChartAt I x₀) x₀ := contMDiffAt_extChartAt
      exact h1.comp_of_eq contMDiffAt_snd rfl
  -- Step 2: `matToBilin` is linear and continuous, hence smooth.
  have hg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E =>
        Work.Diff.EXT.matToBilin (fun i j => Work.Diff.EXT.chartMat G x₀ q.1 q.2 i j))
      ((fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) (t₀, x₀)) := by
    have hmat : ContDiff ℝ (⊤ : ℕ∞) (⇑(Work.Diff.EXT.matToBilin (E := E))) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := MatE (E := E))
        (F := (E →L[ℝ] E →L[ℝ] ℝ)) (n := (⊤ : ℕ∞)) (matToBilin (E := E))
    exact hmat.contDiffAt.comp (t₀, (extChartAt I x₀) x₀) h
  exact hg.comp_contMDiffAt (f := fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) hf

end Work.Diff.EXT
