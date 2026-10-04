import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ricJetDefs
import Submission.Work.Diff.EXT.chartRic_mat_smooth_of_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The chart Ricci matrix is the explicit coordinate expression `ricPhi` in the spatial
`2`-jet of the chart matrix.**  The Ricci components of the Levi-Civita connection of `g` in the
coordinate frame of the chart at `x₀`, as a function of the metric coefficients and their first and
second coordinate derivatives.  `ricPhi` (`Submission/Work/Diff/EXT/ricJetDefs.lean`) is the
explicit universal expression: lowered Koszul Christoffels `jKz`, their derivatives `jKzD`, the
inverse Gram matrix `jInv`, the curvature components `jRm`, and the trace `jRic`.  It is smooth on
`{det ≠ 0}` (separately: `Work.Diff.EXT.ricPhi_contDiffOn`), the region relevant for Riemannian
metrics.  (This is the statement `Work.Diff.EXT.chartRicMat_eq_ricPhi` of
`chartRic_mat_smooth_of_jet.lean` with the existential `Φ` replaced by the explicit `ricPhi`; the
hard geometric input is the coordinate expression for the curvature components, e.g.
`Work.Diff.GE.gRmC_eq_jRm`, `Work.Diff.GE.rmChartExpr_eq`, `Work.Diff.EXT.ricAt_invGram_chart`.)
-/
theorem chartRicMat_ricPhi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] :
    ∀ (x₀ : M) (g : Submission.Diff.SMet I M) (y : E), y ∈ (extChartAt I x₀).target →
      Work.Diff.EXT.chartRicMat g x₀ y =
        Work.Diff.EXT.ricPhi
          (y, Work.Diff.EXT.jet2 (fun p : ℝ × E => Work.Diff.EXT.chartMatFun g x₀ p.2) (0, y)) := by
  classical
  intro x₀ g y hy
  -- the smoothness of the Levi-Civita connection of `g`
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    (Work.Diff.T.lc_smooth (I := I) (M := M) g).1.some
  ext i j
  -- the chart point and its membership in the chart source
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    rw [← extChartAt_source (I := I) (x := x₀)]
    exact (extChartAt I x₀).map_target hy
  have hpy : (extChartAt I x₀) ((extChartAt I x₀).symm y) = y := (extChartAt I x₀).right_inv hy
  -- the left-hand side, as a Ricci trace in the coordinate frame
  rw [show chartRicMat g x₀ y i j
      = Submission.Diff.ricAt (Submission.Diff.lcOf g) ((extChartAt I x₀).symm y)
          (fvec (I := I) x₀ ((extChartAt I x₀).symm y) i)
          (fvec (I := I) x₀ ((extChartAt I x₀).symm y) j) from rfl]
  rw [ricAt_eq_sum_gramInv (I := I) g x₀ (p := (extChartAt I x₀).symm y) hp i j]
  -- the right-hand side, unfolded into the jet expression
  rw [show (ricPhi (E := E)
        (y, jet2 (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y))) i j
      = ∑ k, ∑ l, jInv (chartMatFun g x₀ y) k l *
          jRm (chartMatFun g x₀ y) (fderiv ℝ (chartMatFun g x₀) y)
            (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) k i l j from rfl]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have h2 := gRmC_eq_jRm (I := I) g hcov x₀ hp k i l j
  rw [hpy] at h2
  rw [gmat_symm, h2, jInv]

end Work.Diff.EXT
