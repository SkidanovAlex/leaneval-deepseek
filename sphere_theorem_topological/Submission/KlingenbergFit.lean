import Submission.UniformInj
import Submission.Commons.Analysis.Calculus.exists_uniform_injective_of_hasStrictFDerivAt_of_le

/-!
# The fit lemma: the chart-flow side

Roadmap §130.6 decomposes the *fit lemma* (uniform local injectivity of the exponential map at a
**prescribed** vector `a₀`, the missing input of the attainment) into two general engines
(`Commons.Analysis.Calculus.exists_uniform_injective_of_hasStrictFDerivAt_of_le`,
`Commons.Analysis.Calculus.exists_pos_mul_norm_le_of_isCompact_injective`) and the project-specific
glue.  This file contains the two pieces of the glue that live purely on the chart-flow side:

* `hasStrictFDerivAt_Hfun` — the chart-flow model `Hfun D` is *strictly* differentiable at every
  phase `(x, flowScale D • u)` of the chart data, with derivative `fderiv ℝ (Hfun D) (x, u)`
  (a direct consequence of the joint `C^∞` of `Hfun`);
* `continuousOn_fderiv_Hfun` — the derivative `x ↦ fderiv ℝ (Hfun D) (x, a₀)` is continuous on the
  coordinate image of the compact chart piece (the `hcont` input of the second engine, which turns
  pointwise injectivity of the differential into a *uniform* lower bound).

The remaining glue (the transfer to `GExp x ∘ frameVector z₀ x` and the pointwise differential
injectivity from the conjugate-radius bound) is documented in Roadmap §130.6.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.UniformInj

namespace Submission.KlingenbergFit

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **Strict differentiability of the chart-flow model at a prescribed phase.** -/
theorem hasStrictFDerivAt_Hfun (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hK : (x, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    HasStrictFDerivAt (Hfun D) (fderiv ℝ (Hfun D) (x, u)) (x, u) :=
  (Submission.UniformInj.contDiffAt_Hfun (cov := cov) D hK).hasStrictFDerivAt (by simp)

/-- **Continuity of the derivative of the chart-flow model in the base point.** -/
theorem continuousOn_fderiv_Hfun (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {a₀ : E}
    (hph : ∀ x ∈ (extChartAt I z₀) '' Z, (x, flowScale D • a₀) ∈ chartData (I := I) z₀ Z) :
    ContinuousOn (fun x : E => fderiv ℝ (Hfun D) (x, a₀)) ((extChartAt I z₀) '' Z) := by
  intro x hx
  have h1 : ContinuousAt (fun y : E × E => fderiv ℝ (Hfun D) y) (x, a₀) :=
    (Submission.UniformInj.contDiffAt_Hfun (cov := cov) D (hph x hx)).continuousAt_fderiv (by simp)
  have h2 : Tendsto (fun y : E => (y, a₀)) (𝓝 x) (𝓝 (x, a₀)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have h3 : ContinuousAt (fun y : E => fderiv ℝ (Hfun D) (y, a₀)) x := h1.tendsto.comp h2
  exact h3.continuousWithinAt

end Submission.KlingenbergFit
