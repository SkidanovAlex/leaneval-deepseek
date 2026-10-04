/-
# Layer C2 (DeTurck pull-back): the chart toolkit used by the first-variation computation

This module only *re-exports* the seeded chart machinery that the DeTurck pull-back computation
needs, so that the statements of the lemmas below can be written without importing the seeded
modules one by one:

* `Submission.ChartCurv`: `coordFun` (the chart coordinates of a section), `chrB` (the Christoffel
  symbol as a bilinear form on coordinate vectors), `christoffelEval`-API;
* `Submission.ChartConnection`: `chartGram` (the metric in a chart) and the Leibniz rule
  `hasDerivAt_chartGram` along a curve (metric compatibility, chart form);
* `Submission.Geodesic`: `frameVector`/`frameSection` and `christoffelEval_comm` (torsion-freeness
  in coordinates);
* `Work.Diff.EXT.splice_defs`: `chartMat`/`chartMatFun`, the chart matrix of a (family of) metrics;
* `Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth`: joint smoothness of the chart matrix of
  a jointly smooth family of metrics within a time set;
* `Work.Diff.EXT.hasDerivAt_sliceFDeriv`: Clairaut (Schwarz) in the slice-`fderiv` form.

Nothing is proved here.
-/
import Submission.Work.Diff.STE.C2.Defs
import Submission.ChartCurv
import Submission.ChartConnection
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.hasDerivAt_sliceFDeriv
import Submission.Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.C2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- The chart coordinates of a section in the chart at `x₀` (re-exported vocabulary). -/
noncomputable abbrev coord (x₀ : M) (Z : Π x : M, TangentSpace I x) : M → E :=
  Submission.ChartCurv.coordFun x₀ Z

/-- The vector of `T_pM` with chart coordinates `v` in the chart at `x₀` (re-exported vocabulary). -/
noncomputable abbrev fvec (x₀ p : M) (v : E) : TangentSpace I p :=
  Submission.Geodesic.frameVector x₀ p v

/-- The chart coordinate of a point, in the chart at `x₀`. -/
noncomputable abbrev chartof (x₀ : M) (q : M) : E := (extChartAt I x₀) q

/-- **Pairing a chart matrix with two coordinate vectors**: the bilinear form described by the
matrix `Mmat` in the basis `bB`, evaluated on `a` and `b`.  In other words, if `Mmat` is the chart
matrix of a metric `g` at the point with chart coordinate `y`, then
`matPair Mmat a b = g.inner ((extChartAt I x₀).symm y) (fvec x₀ _ a) (fvec x₀ _ b)`. -/
noncomputable def matPair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Mmat : Work.Diff.EXT.MatE (E := E)) (a b : E) : ℝ :=
  ∑ i, ∑ j, (Work.Diff.EXT.bB.repr a i) * (Work.Diff.EXT.bB.repr b j) * Mmat i j

end Work.Diff.STE.C2
