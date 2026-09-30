/-
# The Koszul identity in charts

For **any** covariant derivative `cov` that is metric-compatible
(`LeanEval.Geometry.SphereTheorem.IsMetricCompatible`) and torsion-free, the chart Christoffel
symbol of `Submission.ChartCurv` satisfies the Koszul formula in chart coordinates:

`chartGram x₀ p (chrB cov x₀ p a b) c = ½ (Dg b a c + Dg a b c − Dg c a b)`,

where `chrB cov x₀ p a b` is the chart-coordinate vector of `∇_{σ_b} σ_a`
(`Submission.ChartCurv.chrB`, following the conventions of `Submission.Geodesic`) and
`Dg x₀ p d a c = Work.Curvature.chartDg x₀ p d a c` is the derivative of the chart metric
component `(a,c)` in the chart direction `d`.

The proof has two steps.

1. **The "star" identity** (`Work.LeviCivita.chartDg_eq_chartGram_chrB`, proved in
   `Submission/Work/LeviCivita/chartDg_eq_chartGram_chrB.lean`): metric compatibility in charts,
   i.e. the product rule `d_v ⟪σ_a, σ_b⟫ = ⟪∇_{σ_v} σ_a, σ_b⟫ + ⟪σ_a, ∇_{σ_v} σ_b⟫`.  No torsion
   hypothesis is needed for this step.
2. **The cyclic algebra** (this file): adding the star identity for `(v,a,b) = (b,a,c)`, `(a,b,c)`
   and subtracting the one for `(c,a,b)`, and using the symmetry of `chartGram` and of `chrB`
   (the latter is torsion-freeness, `Submission.Geodesic.christoffelEval_comm`), leaves exactly
   `2 ⟪∇_{σ_b} σ_a, σ_c⟫`.

This is the form the curvature bridge (`Work.Curvature.curvLe_of_chartModels`) consumes.

Note the hypothesis `[I.Boundaryless]`: the chart-coordinate derivative `Work.Curvature.chartDg` is
an honest derivative only when `(extChartAt I x₀).symm` is smooth *off* its target, i.e. for a
boundaryless model.  (Equivalently one could ask for `I.IsInteriorPoint p`.)  The intended
application `I = 𝓘(ℝ,E4)` is boundaryless.
-/
import Submission.Work.LeviCivita.chartDg_eq_chartGram_chrB

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Geodesic

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

/-- **Torsion-freeness makes `chrB` symmetric** in its two coordinate slots. -/
theorem chrB_comm_of_torsion
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} (htor : cov.torsion = 0)
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (v w : E) :
    chrB cov x₀ p v w = chrB cov x₀ p w v := by
  rw [chrB_apply, chrB_apply]
  exact christoffelEval_comm htor x₀ p hp v w

/-- **The Koszul identity in charts** for a smooth torsion-free metric-compatible connection.

This is the statement the curvature bridge (`Work.Curvature.curvLe_of_chartModels`) needs; see the
module docstring for the proof structure. -/
theorem chartGram_chrB_eq_koszul
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (a b c : E) :
    chartGram (I := I) x₀ p (chrB cov x₀ p a b) c =
      (1/2) * (Work.Curvature.chartDg (I := I) x₀ p b a c
        + Work.Curvature.chartDg (I := I) x₀ p a b c
        - Work.Curvature.chartDg (I := I) x₀ p c a b) := by
  have hstar := fun (v a' b' : E) ↦ chartDg_eq_chartGram_chrB (I := I) hmet x₀ p hp v a' b'
  have hcomm : ∀ v w : E, chrB cov x₀ p v w = chrB cov x₀ p w v :=
    chrB_comm_of_torsion (I := I) htor x₀ p hp
  rw [hstar b a c, hstar a b c, hstar c a b]
  rw [hcomm b a, hcomm c b, hcomm c a]
  rw [chartGram_comm (I := I) x₀ p b (chrB cov x₀ p a c)]
  ring

end

end Work.LeviCivita
