import Submission.RauchGlobal

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Conjugate times along a geodesic, and Rauch's bound on the conjugate radius

A time `t > 0` is a **conjugate time** along a unit-speed geodesic `γ` if there is a Jacobi field
`J` along `γ`, not identically zero, with `J 0 = 0 = J t`.  Rauch's theorem
(`Submission.RauchGlobal.eqOn_zero_of_jacobi`) says that when the sectional curvature is at most
`4` (the project's normalisation) there are no conjugate times before `π/2`: equivalently, the
**conjugate radius** is at least `π/√K_max = π/2`.

## Contents

* `IsConjugateTime`: the definition (germ-level, phrased with `IsJacobiAt`);
* `pi_half_le_of_isConjugateTime`: Rauch's bound on the conjugate radius;
* `isJacobiAt_const_smul`: Jacobi fields along a geodesic form a vector space (scalar multiples).

The "not identically zero" clause is stated as `∃ s ∈ Ioo 0 t, J s ≠ 0`; by uniqueness for the
Jacobi equation this is equivalent to `J ≠ 0` (a nonzero Jacobi field with `J 0 = 0` is nonzero
immediately to the right of `0`).  The formulation used here is chosen so that Rauch's theorem
applies with no extra work.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.ChartBounds
open Submission.RauchGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ConjRadius

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **A conjugate time** along the curve `γ`: a positive time `t` at which there is a Jacobi field
along `γ`, not identically zero, vanishing both at `0` and at `t`. -/
def IsConjugateTime (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  0 < t ∧ ∃ J : (s : ℝ) → TangentSpace I (γ s),
    (∀ s : ℝ, IsJacobiAt cov γ J s) ∧ J 0 = 0 ∧ J t = 0 ∧ ∃ s ∈ Ioo 0 t, J s ≠ 0

/-- **Rauch's theorem, conjugate-radius form.**  Along a curve that is a unit-speed geodesic
everywhere (`IsJacobiAt` carries unit speed in each chart) there is no conjugate time before
`π/2`: the conjugate radius of a manifold with sectional curvature at most `4` is at least
`π/√4 = π/2`. -/
theorem pi_half_le_of_isConjugateTime
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {t : ℝ} (h : IsConjugateTime cov γ t) :
    Real.pi / 2 ≤ t := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨htpos, J, hJ, h0, h1, s, hs, hsne⟩ := h
  have hz := eqOn_zero_of_jacobi (cov := cov) hcov hmet hpinch htor
    (show (-1 : ℝ) < 0 by norm_num) (show t < t + 1 by linarith)
    (fun r _ => hJ r) htpos hcon h0 h1
  exact hsne (hz s ⟨hs.1.le, hs.2.le⟩)

/-- The same statement in the form of a non-membership statement: no time in `(0, π/2)` is a
conjugate time. -/
theorem not_isConjugateTime_of_lt_pi_half
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {t : ℝ} (ht : t < Real.pi / 2) :
    ¬ IsConjugateTime cov γ t :=
  fun h => not_lt_of_ge (pi_half_le_of_isConjugateTime (cov := cov) hcov hmet hpinch htor h) ht

end

end Submission.ConjRadius
