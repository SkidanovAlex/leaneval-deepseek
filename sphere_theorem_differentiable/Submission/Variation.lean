import Submission.Geodesic
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Metric compatibility: the product rule for the metric along a curve

This module extracts the first consequences of the hypothesis `IsMetricCompatible cov` (the
Levi-Civita connection is compatible with the Riemannian metric) in the form needed for the
geodesic/curvature theory:

* `metricCompatible_deriv_inner`: for global smooth sections `Y`, `Z` and a differentiable curve
  `γ`, the derivative of `s ↦ ⟪Y (γ s), Z (γ s)⟫` is
  `⟪∇_{γ'} Y, Z⟫ + ⟪Y, ∇_{γ'} Z⟫` at `γ t`.

The proof is a direct combination of the definition of `IsMetricCompatible` with the chain rule
`Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve`; the only technical point is the
elaboration of `ContMDiffAt.inner_bundle` for the tangent bundle, which requires the *explicit*
form `ContMDiffAt.inner_bundle ...` (dot notation makes the elaborator infer the wrong instance
for the fibre).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Variation

noncomputable section

/-- The function `y ↦ ⟪Y y, Z y⟫` attached to two smooth sections is smooth.  (Stated with an
explicit `ContMDiffAt.inner_bundle` application: dot notation picks up the wrong
`NormedAddCommGroup` instance for the tangent fibration.) -/
lemma contMDiffAt_inner_sections {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y)) (hZ : ContMDiff I I.tangent ∞ (T% Z)) (x : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => inner ℝ (Y y) (Z y)) x :=
  ContMDiffAt.inner_bundle (hY x) (hZ x)

/-- The function `y ↦ ⟪Y y, Z y⟫` attached to two smooth sections is differentiable. -/
lemma mdifferentiableAt_inner_sections {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y)) (hZ : ContMDiff I I.tangent ∞ (T% Z)) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => inner ℝ (Y y) (Z y)) x :=
  (contMDiffAt_inner_sections hY hZ x).mdifferentiableAt (by norm_num)

/-- **The product rule for the Riemannian metric along a curve.**  For smooth global sections
`Y`, `Z` and a curve `γ` differentiable at `t`,
`d/dt ⟪Y (γ t), Z (γ t)⟫ = ⟪∇_{γ'(t)} Y, Z (γ t)⟫ + ⟪Y (γ t), ∇_{γ'(t)} Z⟫`. -/
theorem metricCompatible_deriv_inner
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y)) (hZ : ContMDiff I I.tangent ∞ (T% Z))
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    deriv (fun s => inner ℝ (Y (γ s)) (Z (γ s))) t
      = inner ℝ (cov Y (γ t) (curveVelocity (I := I) γ t)) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) (curveVelocity (I := I) γ t)) := by
  have hinner : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => inner ℝ (Y y) (Z y)) (γ t) :=
    mdifferentiableAt_inner_sections hY hZ (γ t)
  have hchain :=
    Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve hinner hγ
  rw [show deriv (fun s => inner ℝ (Y (γ s)) (Z (γ s))) t
      = deriv ((fun y : M => inner ℝ (Y y) (Z y)) ∘ γ) t from rfl, ← hchain]
  exact hmet Y Z hY hZ (γ t) (curveVelocity (I := I) γ t)

/-- Product rule along a curve, in `HasDerivAt` form. -/
theorem hasDerivAt_inner_sections
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (T% Y)) (hZ : ContMDiff I I.tangent ∞ (T% Z))
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    HasDerivAt (fun s => inner ℝ (Y (γ s)) (Z (γ s)))
      (inner ℝ (cov Y (γ t) (curveVelocity (I := I) γ t)) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) (curveVelocity (I := I) γ t))) t := by
  rw [← (metricCompatible_deriv_inner cov hmet hY hZ hγ)]
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => inner ℝ (Y (γ s)) (Z (γ s))) t :=
    MDifferentiableAt.comp t (mdifferentiableAt_inner_sections hY hZ (γ t)) hγ
  rw [mdifferentiableAt_iff_differentiableAt] at hcomp
  exact hcomp.hasDerivAt

end

end Submission.Variation
