/-
# Smoothness of a form prescribed in a chart, read in the frame at a point

Let `x₀` be a chart centre and `W : ℝ × E → MatE` a smooth (in the model space!) matrix-valued
function of time and chart coordinate.  For a point `x` in the chart at `x₀` we consider

`p ↦ frameMat x p.2 (formInFrame x₀ p.2 (fun i j => W (p.1, (extChartAt I x₀) p.2) i j))`,

i.e.: build the bilinear form on `T_{p.2}M` whose matrix in the coordinates of the chart at `x₀`
is the prescribed matrix `W (p.1, chart_{x₀} p.2)`, and then read *that same form* in the frame of
the chart at `x`.  The lemma says this matrix-valued function of `p : ℝ × M` is `C^∞` at `(τ, x)`.

This is exactly the local smoothness input that the glue/restart construction
(`Work.Diff.EXT.glue_local_metric_families`) needs: it is handed a local *chart matrix* `W` of a
metric family and must produce the *matrix in the frame at an arbitrary point* of the assembled
global form.

## The proof

`formInFrame_apply` computes the value of `formInFrame x₀ y A` on two tangent vectors in terms of
the coordinate functionals of the chart at `x₀`.  Applied to the frame vectors of the chart at `x`
(`frameVector x y (bB i)`), the `(i,j)`-th entry of the matrix becomes the finite sum

`∑ k, ∑ l, W (t, chart_{x₀} y) k l * coord k (frameCoords_{x₀} y (frameVector_x y (bB i)))
                             * coord l (frameCoords_{x₀} y (frameVector_x y (bB j)))`.

Both factors are smooth in `p = (t, y)`:

* `W (t, chart_{x₀} y)` is the composition of `W` (smooth at `(τ, chart_{x₀} x)` by hypothesis)
  with the smooth map `p ↦ (p.1, (extChartAt I x₀) p.2)` (`contMDiffAt_extChartAt'`, using
  `x ∈ (chartAt H' x₀).source`);
* `coord k (frameCoords_{x₀} y (frameVector_x y (bB i)))` is smooth because the *coordinates* of a
  smooth section in a chart are smooth (`contMDiffAt_clmAt_apply` below, a metric-free version of
  `Submission.Geodesic.contMDiffAt_continuousLinearMapAt_apply`) and `y ↦ frameVector_x y (bB i)`
  is a smooth section on the chart at `x` (`Work.Diff.EXT.contMDiffAt_frameVector`).

Sums and products then give the smoothness of the assembled matrix.
-/

import Mathlib
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.bilinMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.FrameKit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The coordinates of a smooth section in a chart are smooth.**

If `Z` is a smooth section of the tangent bundle at `x` and `x` lies in the chart at `x₀`, then
`y ↦ frameCoords x₀ y (Z y)` -- the coordinates of `Z y` in the coordinate frame of the chart at
`x₀` -- is `C^∞` at `x`.

This is `Submission.Geodesic.contMDiffAt_continuousLinearMapAt_apply` with the instance Riemannian
metric (and `T2Space M`) removed from the hypotheses, which is what working with an explicit family
of metrics requires. -/
lemma contMDiffAt_clmAt_apply (x₀ : M) {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt ∞ (T% Z) x) (hx : x ∈ (chartAt H' x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)) x := by
  have hsec := (Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) x₀) (by simpa using hx)).mp hZ
  refine hsec.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [Trivialization.continuousLinearMapAt_apply_of_mem
    (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy]

/-- The frame vectors of the chart at `x`, expressed in the coordinates of the chart at `x₀`, are
smooth at `x`. -/
lemma contMDiffAt_frameCoords_frameVector (x₀ x : M) (i : Fin (Module.finrank ℝ E))
    (hx : x ∈ (chartAt H' x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : M => Work.Diff.EXT.frameCoords (I := I) x₀ y
      (Submission.Geodesic.frameVector (I := I) x y (Work.Diff.EXT.bB (E := E) i))) x :=
  contMDiffAt_clmAt_apply x₀
    (Work.Diff.EXT.contMDiffAt_frameVector (I := I) x (Work.Diff.EXT.bB (E := E) i)
      (mem_chart_source H' x)) hx

theorem frameMat_of_chartData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {x₀ x : M} {W : ℝ × E → Work.Diff.EXT.MatE (E := E)} {τ : ℝ}
    (hx : x ∈ (chartAt H' x₀).source)
    (hW : ContDiffAt ℝ (⊤ : ℕ∞) W (τ, (extChartAt I x₀) x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun p : ℝ × M => Work.Diff.EXT.frameMat (I := I) x p.2
        (Work.Diff.EXT.formInFrame (I := I) x₀ p.2
          (fun i j => W (p.1, (extChartAt I x₀) p.2) i j)))
      (τ, x) := by
  classical
  -- the frame vectors of the chart at `x`, in the coordinates of the chart at `x₀`
  let V : Fin (Module.finrank ℝ E) → ℝ × M → E := fun i p =>
    Work.Diff.EXT.frameCoords (I := I) x₀ p.2
      (Submission.Geodesic.frameVector (I := I) x p.2 (Work.Diff.EXT.bB (E := E) i))
  have hsnd : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I ∞
      (Prod.snd : ℝ × M → M) (τ, x) := contMDiffAt_snd
  have hVsm : ∀ i, ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, E) ∞ (V i) (τ, x) := by
    intro i
    exact ContMDiffAt.comp (f := (Prod.snd : ℝ × M → M))
      (g := fun y : M => Work.Diff.EXT.frameCoords (I := I) x₀ y
        (Submission.Geodesic.frameVector (I := I) x y (Work.Diff.EXT.bB (E := E) i)))
      (τ, x) (contMDiffAt_frameCoords_frameVector (I := I) (E := E) x₀ x i hx) hsnd
  -- the coordinate map `p ↦ (p.1, (extChartAt I x₀) p.2)` is smooth at `(τ, x)`
  have hfst : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => p.1) (τ, x) := contMDiffAt_fst
  have hχsnd : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => (extChartAt I x₀) p.2) (τ, x) :=
    ContMDiffAt.comp (f := (Prod.snd : ℝ × M → M)) (g := fun y : M => (extChartAt I x₀) y)
      (τ, x) (contMDiffAt_extChartAt' (I := I) (x := x₀) (x' := x) hx) hsnd
  have hχ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) (τ, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hfst.prodMk hχsnd
  have hWc : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (𝓘(ℝ, MatE (E := E))) ∞
      (fun p : ℝ × M => W (p.1, (extChartAt I x₀) p.2)) (τ, x) :=
    ContDiffAt.comp_contMDiffAt (F := ℝ × E) (F' := MatE (E := E))
      (M := ℝ × M) (x := (τ, x))
      (f := fun p : ℝ × M => (p.1, (extChartAt I x₀) p.2)) (g := W) hW hχ
  -- the entries of `W (p.1, chart p.2)`
  have hentry : ∀ k l : Fin (Module.finrank ℝ E),
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => W (p.1, (extChartAt I x₀) p.2) k l) (τ, x) := by
    intro k l
    exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hWc k) l
  -- the coordinate functionals applied to the frame vectors
  have hcoord : ∀ k i : Fin (Module.finrank ℝ E),
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Work.Diff.EXT.bCoordCLM (E := E) k (V i p)) (τ, x) := by
    intro k i
    exact (Work.Diff.EXT.bCoordCLM (E := E) k).contMDiffAt.comp (τ, x) (hVsm i)
  -- the assembled matrix is smooth
  have hG : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) 𝓘(ℝ, MatE (E := E)) ∞
      (fun p : ℝ × M => fun i j => ∑ k, ∑ l,
        W (p.1, (extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
          Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) (τ, x) := by
    rw [contMDiffAt_pi_space]
    intro i
    rw [contMDiffAt_pi_space]
    intro j
    refine ContMDiffAt.sum (t := Finset.univ) (f := fun k p => ∑ l,
      W (p.1, (extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
        Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) ?_
    intro k hk
    refine ContMDiffAt.sum (t := Finset.univ) (f := fun l p =>
      W (p.1, (extChartAt I x₀) p.2) k l * Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
        Work.Diff.EXT.bCoordCLM (E := E) l (V j p)) ?_
    intro l hl
    exact ((hentry k l).mul (hcoord k i)).mul (hcoord l j)
  -- ... and it is the matrix we want, by `formInFrame_apply`
  have hFG : ∀ p : ℝ × M, Work.Diff.EXT.frameMat (I := I) x p.2
        (Work.Diff.EXT.formInFrame (I := I) x₀ p.2
          (fun i j => W (p.1, (extChartAt I x₀) p.2) i j))
      = fun i j => ∑ k, ∑ l, W (p.1, (extChartAt I x₀) p.2) k l *
          Work.Diff.EXT.bCoordCLM (E := E) k (V i p) *
          Work.Diff.EXT.bCoordCLM (E := E) l (V j p) := by
    intro p
    funext i j
    rw [Work.Diff.EXT.frameMat]
    rw [Work.Diff.EXT.formInFrame_apply]
    rfl
  exact hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hFG)

end Work.Diff.EXT.FrameKit
