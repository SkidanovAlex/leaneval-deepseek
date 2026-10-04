import Submission.Work.OddBound.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound

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

/-- **Smoothness of the product of a smooth scalar function with a field smooth along `γ`.**
`chartCoords` is (pointwise) linear in the field, so this reduces to `ContDiffOn.smul` on the fixed
neighbourhood given by `SmoothAlongAt hX`.  The scalar hypothesis is `ContDiffOn ℝ ∞ f U` on an open
`U ∋ t` (NOT `ContDiffAt ℝ ∞ f t`, which for `n = ∞` only gives order-by-order shrinking
neighbourhoods). -/
theorem smoothAlongAt_smul_varying
    {γ : ℝ → M} {X : (t : ℝ) → TangentSpace I (γ t)} {f : ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (htU : t ∈ U)
    (hX : SmoothAlongAt (I := I) γ X t) (hf : ContDiffOn ℝ ∞ f U) :
    SmoothAlongAt (I := I) γ (fun s => f s • X s) t := by
  obtain ⟨V, hVopen, htV, hVsrc, hVcd⟩ := hX
  refine ⟨U ∩ V, hU.inter hVopen, ⟨htU, htV⟩, fun s hs => hVsrc s hs.2, ?_⟩
  have heq : (Submission.JacobiCoords.chartCoords (I := I) (γ t) γ fun s => f s • X s)
      = fun s => f s • Submission.JacobiCoords.chartCoords (I := I) (γ t) γ X s := by
    funext s
    exact map_smul ((trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s))
      (f s) (X s)
  rw [heq]
  exact (hf.mono fun s hs => hs.1).smul (hVcd.mono fun s hs => hs.2)


end Work.OddBound
