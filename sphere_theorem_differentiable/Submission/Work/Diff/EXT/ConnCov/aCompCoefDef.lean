import Mathlib
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_aOfTower
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.chartMat_fderiv_basis
import Submission.Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coefficient of the first chart derivative of the chart matrix, from the connection difference

This module only collects the *definition* `Work.Diff.EXT.ConnCov.aCompCoef` used by
`Work.Diff.EXT.ConnCov.chartMat_jets_of_aComp_jets` (and by the induction step
`Work.Diff.EXT.ConnCov.aCompCoef_succ_bound`), so that the two modules do not have to import each
other.

`aCompCoef G x₀ t i j m y` is the explicit expression of the first chart derivative of the chart
matrix in terms of the chart array `aComp` of the *lowered* connection difference
`g_t(∇^{g_t} − ∇^{g_0})` and of the *fixed* Christoffel symbols of `G 0`:

`∂_m g_{ij} = aComp_{mij} + aComp_{mji} + Σ_p (g_{ip}Γ0^p_{mj} + g_{jp}Γ0^p_{mi})`.

No inverse metric occurs, so no ellipticity is needed.  The identity itself is proved in
`Work.Diff.EXT.ConnCov.fderiv_chartMat_eq_aComp_coef`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The coefficient of the first derivative of the chart matrix**, read off from `aComp` and from
the Christoffel symbols `Γ0` of the *fixed* metric `G 0`:
`∂_m g_{ij} = aComp_{mij} + aComp_{mji} + Σ_p (g_{ip}Γ0^p_{mj} + g_{jp}Γ0^p_{mi})`. -/
noncomputable def aCompCoef (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j m : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    (Work.Diff.EXT.aComp G x₀ t y m i j + Work.Diff.EXT.aComp G x₀ t y m j i)
      + ∑ p : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
            + Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) j p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i)

/-- The defining expansion of `aCompCoef` (the two `aComp` summands and the `Γ0`-products). -/
theorem aCompCoef_eq_sum (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j m : Fin (Module.finrank ℝ E)) (y : E) :
    aCompCoef (I := I) (M := M) G x₀ t i j m y
      = (Work.Diff.EXT.aComp G x₀ t y m i j + Work.Diff.EXT.aComp G x₀ t y m j i)
        + ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p
                * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
              + Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) j p
                * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i) := rfl

end Work.Diff.EXT.ConnCov
