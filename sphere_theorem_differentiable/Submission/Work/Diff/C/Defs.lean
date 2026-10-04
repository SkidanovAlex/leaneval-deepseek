import Mathlib
import Submission.Diff.Interfaces
import Submission.Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric
import Submission.Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric
import Submission.Commons.Geometry.Manifold.Riemannian.contMDiff_inner_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C (classical high-pinching sphere theorem): shared definitions

This module is the vocabulary of area C.  It defines

* the **instance-free** forms `PinchedFor g cov κ Λ` / `IsMetricCompatibleFor g cov` of the frozen
  contracts `Submission.Diff.Pinched` / `Submission.Diff.IsMetricCompatible` (so that the scaled
  metric of the reduction to the normalisation `1 < K ≤ 1 + η` can be discussed while the ambient
  instance is the original metric), together with the definitional `iff`s;
* the Riemannian **distance** `rdist p ·` as a real function, and the **gradient** `rgrad F` of a
  real-valued function on `M` (via the Riesz isomorphism `InnerProductSpace.toDual`).

Nothing here is a `sorry`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The instance-free form of `Submission.Diff.Pinched`.**  The inner products are spelled out
through `g.inner`, so that the predicate can be used with a metric different from the ambient
instance. -/
def PinchedFor (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (κ Λ : ℝ) : Prop :=
  ∀ (X Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) → ∀ x : M,
    g.inner x (X x) (X x) = (1 : ℝ) → g.inner x (Y x) (Y x) = (1 : ℝ) →
    g.inner x (X x) (Y x) = (0 : ℝ) →
    κ < g.inner x (curv cov X Y Y x) (X x) ∧ g.inner x (curv cov X Y Y x) (X x) ≤ Λ

/-- **The instance-free form of `Submission.Diff.IsMetricCompatible`.** -/
def IsMetricCompatibleFor (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y Z : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M ↦ g.inner y (Y y) (Z y)) x v =
        g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)

section Instance

variable [hamb : RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The instance-free form agrees with `Pinched`. -/
theorem pinchedFor_iff (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (κ Λ : ℝ) : Pinched cov κ Λ ↔ PinchedFor hamb.g cov κ Λ := Iff.rfl

/-- The instance-free form agrees with `IsMetricCompatible`. -/
theorem isMetricCompatibleFor_iff
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    IsMetricCompatible cov ↔ IsMetricCompatibleFor hamb.g cov := Iff.rfl

end Instance

/-! ## The distance function and the gradient -/

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian distance from `p` to `x`, as a real-valued function on `M`
(`0` where the extended distance is infinite). -/
noncomputable def rdist (p : M) (x : M) : ℝ := (Manifold.riemannianEDist I p x).toReal

/-- The **gradient** of a real-valued function, as a tangent vector: the Riesz representative of
the manifold derivative. -/
noncomputable def rgrad (F : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm
    (mfderiv I (𝓘(ℝ, ℝ)) F x)

/-- The **Hessian** of a real-valued function, as a symmetric bilinear form: the covariant
derivative of the gradient, paired with the second vector. -/
noncomputable def rhess (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (F : M → ℝ) (x : M) (V W : TangentSpace I x) : ℝ :=
  inner ℝ (cov (fun y : M ↦ rgrad F y) x V) W

/-- The defining property of the gradient: `⟨∇F, v⟩ = dF(v)`. -/
theorem inner_rgrad (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (rgrad F x) v = mfderiv I (𝓘(ℝ, ℝ)) F x v :=
  InnerProductSpace.toDual_symm_apply

end Work.Diff.C
