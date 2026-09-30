import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.ChartConnection
import Submission.Work.Curvature.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Part 2 of the curvature contract — the chart bridge (definition layer)

The blueprint's `LC` area proves the Koszul formula in charts for a smooth, torsion-free,
metric-compatible connection `cov`:

`chartGram x₀ p (chrB cov x₀ p a b) c = ½ (Dg x₀ p b a c + Dg x₀ p a b c − Dg x₀ p c a b)`

where `Dg x₀ p d a c` is the derivative of `q ↦ chartGram x₀ ((extChartAt I x₀).symm q) a c` at
`extChartAt I x₀ p` in the direction `d`.  This file provides that derivative as
`Work.Curvature.chartDg` and the *change of variables* `chartDg_eq_dG` that compares it with the
derivative `dG` of a model metric field of Part 1: if the chart metric agrees with the model `G`
near the chart image of `p`, then `chartDg = dG`.

The remaining plumbing of the bridge (from the chart Koszul identity to `RauchK.CurvLe`) is
delegated to `Work.Curvature.curvLe_of_chartModels`.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Curvature

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- The `Dg` of the blueprint: the derivative of the chart metric component `a c` in the chart
coordinates at `x₀`, at the point `extChartAt I x₀ p`, in the direction `d`. -/
noncomputable def chartDg (x₀ p : M) (d a c : E) : ℝ :=
  fderiv ℝ (fun q : E =>
      Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a c)
    (extChartAt I x₀ p) d

end

section E4

variable
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E4 H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E4 (fun (x : M) ↦ TangentSpace I x)]

/-- **Change of variables for the chart derivative.**  If the chart metric agrees with the model
metric field `G` (of Part 1) on a neighbourhood of the chart image of `x₀`, then the chart
derivative `chartDg` is the model derivative `dG`. -/
theorem chartDg_eq_dG {G : MetricField} (x₀ p : M) (d a c : E4)
    (h : ∀ᶠ q in nhds (extChartAt I x₀ p),
      Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a c = G q a c) :
    chartDg (I := I) x₀ p d a c = dG G (extChartAt I x₀ p) d a c := by
  have h' : (fun q : E4 =>
        Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a c)
      =ᶠ[nhds (extChartAt I x₀ p)] fun q : E4 => G q a c := h
  rw [chartDg, dG, h'.fderiv_eq]

end E4

end Work.Curvature
