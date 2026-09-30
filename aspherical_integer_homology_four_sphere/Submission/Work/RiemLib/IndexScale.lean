import Submission.Work.RiemLib.IndexFTC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.JacobiCoords
open Submission.BonnetMyers
open Submission.IntrinsicVariation
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2
open Submission.IndexIntrinsic3
open Submission.IndexCorner2
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.JacobiGlobal

/-!
# Homogeneity of the objects of the index form

The three scaling lemmas needed by the energy side of `σ ≤ κ` (Roadmap §102.6 (ii)): the chart
coordinates of a field, the covariant derivative `covAlong`, and the intrinsic index integrand
`idxAlong` are homogeneous in the field. -/

namespace Submission.IndexScale

noncomputable section

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

/-- The chart coordinates of a field are homogeneous in the field. -/
lemma chartCoords_smul (z : M) (γ : ℝ → M) (V : (t : ℝ) → TangentSpace I (γ t)) (c : ℝ) :
    chartCoords (I := I) z γ (fun t => c • V t) = fun t => c • chartCoords (I := I) z γ V t := by
  funext t
  exact map_smul ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ (γ t)) c (V t)

/-- `deriv` commutes with scalar multiplication (unconditionally: for `c = 0` both sides vanish,
and for `c ≠ 0` differentiability is preserved). -/
lemma deriv_const_smul_all (c : ℝ) (f : ℝ → E) (x : ℝ) :
    deriv (fun s => c • f s) x = c • deriv f x := by
  by_cases hd : DifferentiableAt ℝ f x
  · exact deriv_const_smul c hd
  · by_cases hc : c = 0
    · subst hc
      simp
    · rw [deriv_zero_of_not_differentiableAt hd, smul_zero]
      have : ¬ DifferentiableAt ℝ (fun s => c • f s) x := by
        intro h
        refine hd ?_
        have h2 : DifferentiableAt ℝ (fun s => c⁻¹ • (c • f s)) x := h.const_smul c⁻¹
        have heq : (fun s : ℝ => c⁻¹ • (c • f s)) = f := by
          funext s
          calc c⁻¹ • (c • f s) = (c⁻¹ * c) • f s := smul_smul c⁻¹ c (f s)
            _ = (1 : ℝ) • f s := by rw [inv_mul_cancel₀ hc]
            _ = f s := one_smul ℝ (f s)
        rwa [heq] at h2
      rw [deriv_zero_of_not_differentiableAt this]

/-- `covAlong` is homogeneous in the field. -/
lemma covAlong_smul (htor : cov.torsion = 0) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace I (γ t)) (c : ℝ) (t : ℝ) :
    covAlong cov (fun s => c • V s) t = c • covAlong cov V t := by
  rw [covAlong, covAlong, chartCoords_smul]
  have hderiv : deriv (fun s : ℝ => c • chartCoords (I := I) (γ t) γ V s)
      = fun s : ℝ => c • deriv (chartCoords (I := I) (γ t) γ V) s := by
    funext s
    exact deriv_const_smul_all c (chartCoords (I := I) (γ t) γ V) s
  rw [hderiv, DtQ_smul]
  simp only [frameVector, map_smul]

/-- `idxAlong` is homogeneous of degree two in the field. -/
lemma idxAlong_smul (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (γ : ℝ → M)
    (V Z : (t : ℝ) → TangentSpace I (γ t)) (c : ℝ) (t : ℝ) :
    idxAlong (cov := cov) γ (fun s => c • V s) (fun s => c • Z s) t
      = c ^ 2 * idxAlong (cov := cov) γ V Z t := by
  simp only [idxAlong, curvVec_smul_left (cov := cov) ‹ContMDiffCovariantDerivative cov ∞›,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  ring

end

end Submission.IndexScale
