import Submission.Pinch

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The upper pinching bound `K ≤ 4`

`QuarterPinched cov` says that the sectional curvature of every plane lies in Knill's interval
`(1, 4]`.  `Submission/Pinch.lean` extracts the **lower** bound `1 ≤ ⟪R(σ_a,σ_b)σ_b,σ_a⟫` for an
orthonormal pair of coordinate vectors; this file extracts the **upper** bound
`⟪R(σ_a,σ_b)σ_b,σ_a⟫ ≤ 4` in the same two forms (curvature on tangent vectors, curvature in the
chart metric).

The upper bound is the input of

* Rauch's comparison theorem in its "no conjugate points before `π/√K_max`" form
  (`2 = √4`, i.e. all geodesics are free of conjugate points up to length `π/2` in the project's
  normalisation `K ∈ (1,4]`);
* the Synge/Klingenberg shortening argument for closed geodesics (the second variation
  `∫ (‖∇X‖² - ⟪R(X,γ')γ',X⟫)` is negative as soon as `‖∇X‖` is small compared with `4 ‖X‖²`).

Nothing in the statement refers to the `(1,4]` bounds other than through `QuarterPinched`.
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Curvature
open Submission.CurvatureVec
open Commons.Geometry.Manifold.VectorField
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.PinchUpper

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The upper pinching bound in the frame.**  If `σ_a = frameVector x₀ p a` and
`σ_b = frameVector x₀ p b` are orthonormal at `p`, the sectional curvature of the plane they span
is at most `4`. -/
theorem inner_curvVec_le_four
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x₀ p : M} {a b : E}
    (ha : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) = 1)
    (hb : inner ℝ (frameVector (I := I) x₀ p b) (frameVector (I := I) x₀ p b) = 1)
    (hab : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) = 0) :
    inner ℝ (frameVector (I := I) x₀ p a)
      (curvVec cov p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p b)) ≤ 4 := by
  obtain ⟨X, hX, hXp⟩ :=
    exists_contMDiff_section_apply_eq (I := I) (M := M) (frameVector (I := I) x₀ p a)
  obtain ⟨Y, hY, hYp⟩ :=
    exists_contMDiff_section_apply_eq (I := I) (M := M) (frameVector (I := I) x₀ p b)
  have h1 : ‖X p‖ = 1 := by
    have hsq : ‖X p‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hXp]
      exact ha
    nlinarith [norm_nonneg (X p)]
  have h2 : ‖Y p‖ = 1 := by
    have hsq : ‖Y p‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hYp]
      exact hb
    nlinarith [norm_nonneg (Y p)]
  have h3 : inner ℝ (X p) (Y p) = 0 := by
    rw [hXp, hYp]
    exact hab
  have hpin := (quarterPinched_curvForm_unit cov hcov hmet hpinch hX hY h1 h2 h3).2
  rw [← curvFormVec_eq cov hcov hX hY hXp hYp] at hpin
  rw [← inner_curvVec_self cov hcov p (frameVector (I := I) x₀ p a)
    (frameVector (I := I) x₀ p b)] at hpin
  rw [real_inner_comm] at hpin
  linarith

/-- The upper pinching bound with the hypotheses phrased through the chart metric. -/
theorem chartGram_curvVec_le_four
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x₀ p : M} {a b : E}
    (ha : chartGram (I := I) x₀ p a a = 1) (hb : chartGram (I := I) x₀ p b b = 1)
    (hab : chartGram (I := I) x₀ p a b = 0) :
    inner ℝ (frameVector (I := I) x₀ p a)
      (curvVec cov p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p b)) ≤ 4 :=
  inner_curvVec_le_four (cov := cov) hcov hmet hpinch ha hb hab

end

end Submission.PinchUpper
