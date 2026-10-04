import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.smp_defs
import Submission.Curvature
import Submission.CurvatureVec
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_cyclic_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for the Bianchi + Kato area (`Work.Diff.GE.bianchi_kato`)

This module collects the frozen definitions of the sphere-theorem project
(`Submission.Diff.Interfaces`, `Submission.Diff.Alg`, `Submission.Diff.Grad`) together with the
elementary bridges between them and the seeded curvature library (`Submission.CurvatureVec`), and
the definitions used by the proof of `BianchiKato`.

Main contents

* `Work.Diff.GE.exists_isONFrame`, `Work.Diff.GE.isONFrame_onFrame` : orthonormal frames exist and
  the chosen frame `onFrame g x` is one;
* `Work.Diff.GE.smoothExt_spec` : the chosen extension `smoothExt x u` is smooth with `smoothExt x u x = u`;
* `Work.Diff.GE.rmVec_eq_curvVec_lcOf`, `Work.Diff.GE.rmP_eq` : `rmVec`/`rmP` of the frozen interface are
  the seeded curvature tensor `curvVec`;
* `Work.Diff.GE.covDir`, `Work.Diff.GE.dRSec` : the covariant derivative `∇_U σ` of a section and the
  covariant derivative `(∇_U R)(X,Y)Z` of the curvature tensor, as sections.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Finset
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.CurvatureVec
open Submission.Curvature

namespace Work.Diff.GE

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

-- exists_isONFrame / isONFrame_onFrame now come from Submission.Work.Diff.GE.curvbasic (lead, dedup 2026-09-30)
-- smoothExt_spec now comes from Submission.Work.Diff.GE.smp_defs (lead dedup)

/-- `rmVec` is the seeded curvature tensor `curvVec`. -/
theorem rmVec_eq_curvVec_lcOf (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞)
    (x : M) (u v w : TangentSpace I x) :
    rmVec (lcOf g) x u v w = curvVec (lcOf g) x u v w := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [show rmVec (lcOf g) x u v w
      = curv (lcOf g) (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl]
  rw [curvVec_eq (lcOf g) hcov (smoothExt_spec (I := I) x u).1 (smoothExt_spec (I := I) x v).1
      (smoothExt_spec (I := I) x w).1 (smoothExt_spec (I := I) x u).2 (smoothExt_spec (I := I) x v).2
      (smoothExt_spec (I := I) x w).2]

/-- `rmP` is the curvature tensor paired with its last two arguments. -/
theorem rmP_eq (g : SMet I M) (hcov : ContMDiffCovariantDerivative (lcOf g) ∞)
    (x : M) (a b c d : TangentSpace I x) :
    rmP g x a b c d = g.inner x (curvVec (lcOf g) x a b d) c := by
  rw [show rmP g x a b c d = g.inner x (rmVec (lcOf g) x a b d) c from rfl,
    rmVec_eq_curvVec_lcOf g hcov x a b d]

end Basic

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `∇_U σ`, the covariant derivative of the section `σ` in the direction of the field `U`. -/
noncomputable def covDir (g : SMet I M) (U σ : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y :=
  fun p => lcOf g σ p (U p)

/-- `(∇_U R)(X,Y)Z = ∇_U(R(X,Y)Z) - R(∇_UX,Y)Z - R(X,∇_UY)Z - R(X,Y)∇_UZ`, the covariant derivative
of the curvature tensor of the Levi-Civita connection of `g`, as a section. -/
noncomputable def dRSec (g : SMet I M) (U X Y Z : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace I y :=
  fun p => lcOf g (curv (lcOf g) X Y Z) p (U p)
    - curv (lcOf g) (covDir g U X) Y Z p
    - curv (lcOf g) X (covDir g U Y) Z p
    - curv (lcOf g) X Y (covDir g U Z) p

/-- Metric compatibility of the Levi-Civita connection `lcOf g` with respect to `g` itself, phrased
without the typeclass-argument friction of the frozen `IsMetricCompatible` (the instance metric is
set to `g`). This is exactly the third component of the contract `LCSmooth I M`. -/
def MetricCompat (g : SMet I M) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  IsMetricCompatible (lcOf g)

/-- The trace-free part of the curvature array `rmC g x`, in the `Iso`-decomposition
`R° = R - (S/(n(n-1))) Iso n`. -/
noncomputable def tfRm (g : SMet I M) (x : M) : Curv4 (Module.finrank ℝ E) :=
  fun i j k l => rmC g x i j k l -
    (scalAt g x / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))) *
      Iso (Module.finrank ℝ E) i j k l

/-- The trace-free part of the array `(∇_v Rm)_{ijkl}` of first covariant derivatives of the
curvature tensor, in the same `Iso`-decomposition (its trace is `∇_v S`). -/
noncomputable def tfDRm (g : SMet I M) (x : M) (v : TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l) -
    ((∑ i', ∑ j', covRm g x v (onFrame g x i') (onFrame g x j') (onFrame g x i')
        (onFrame g x j')) /
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))) *
      Iso (Module.finrank ℝ E) i j k l

end Defs

end Work.Diff.GE
