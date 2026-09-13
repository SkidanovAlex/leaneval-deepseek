/-
Proposition 3.1 of Shankar--Yuan (Alexandrov regularity), reduced to three inputs:

* `GradientEstimateInput` -- Trudinger--Wang's weighted interior gradient estimate for viscosity
  solutions of `σ₂ = 1` with `Δu ≥ 0` (used in the form of the pointwise estimate `(point)` of
  Section 3 of the paper),
* `WeakHessianMeasureInput` -- Chaudhuri--Trudinger's theorem that the weak Hessian of a
  `2`-convex continuous function is a vector Radon measure (together with the existence of the
  weak gradient in `L¹_loc`),
* `TaylorCoreInput` -- the analytic core, i.e. the paper's Lemma `lem:o(r²)` of the appendix
  (formalised in `Submission/AlexandrovCore.lean`).

The remaining ingredients -- Lebesgue's differentiation theorem, the density theorem for the
singular part of a measure, and the abstract lemma `lem:pto(r²)` -- are all in Mathlib or in the
commons.
-/
import Mathlib
import Submission.AlexandrovCore
import Submission.ViscosityAffine
import Submission.MasterEstimate
import Submission.Commons.Analysis.MeasureTheory.Lebesgue.sup_le_of_average_and_slope_lt_four
import Submission.Commons.Measure.Lebesgue.sup_le_of_average_and_slope
import Submission.Commons.Measure.Lebesgue.ae_isLebesguePoint
import Submission.Commons.Measure.Lebesgue.ae_isLebesguePoint_vec
import Submission.Commons.Measure.Lebesgue.ae_isVanishingPoint
import Submission.Commons.Analysis.Sigma2.pairSum_nonneg_of_sqrt_le_sum
import Submission.Commons.Analysis.Sigma2.pairSum_nonneg_of_sqrt_le_sum_fin

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- `u` is `2`-convex on `s` in the viscosity sense: `Δu ≥ 0` and `σ₂(D²u) ≥ 0` in the viscosity
sense. -/
def IsTwoConvexOn (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) : Prop :=
  IsViscSubsolution negTrace u s ∧ IsViscSubsolution (fun M => -(σ₂ M)) u s

/-- **Trudinger--Wang's weighted interior gradient estimate** for viscosity solutions of `σ₂ = 1`
with `Δu ≥ 0`, in the form used in Section 3 of Shankar--Yuan: for `g` a continuous viscosity
solution on the open set `s`, and `ball x (2r) ⊆ s`,
`r^5 |g y - g z| / |y - z| ≤ C ∫_{ball x (2r)} |g|` for all `y z ∈ ball x r`. -/
def GradientEstimateInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ⁴ → ℝ) (s : Set ℝ⁴), IsOpen s → ContinuousOn g s →
    IsViscSolution (fun M => -Gop M) g s → IsViscSubsolution negTrace g s →
    ∀ (x : ℝ⁴) (r : ℝ), 0 < r → closedBall x (2 * r) ⊆ s →
      ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r, y ≠ z →
        r ^ 5 * |g y - g z| / dist y z ≤ C * ∫ w in ball x (2 * r), |g w|

/-- **Chaudhuri--Trudinger**: a continuous `2`-convex function has a weak gradient in `L¹_loc` and
its weak Hessian is a matrix valued Radon measure, which we write as `M dx + σ` with `M ∈ L¹_loc`
the density of the absolutely continuous part and `σ` the singular part. -/
def WeakHessianMeasureInput : Prop :=
  ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴), IsOpen s → ContinuousOn u s → IsTwoConvexOn u s →
    ∃ (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴),
      LocallyIntegrable G volume ∧ (∀ i j, LocallyIntegrable (M i j) volume) ∧
      (∀ i j, (σ i j).totalVariation ⟂ₘ volume) ∧
      HasWeakGradient u s G ∧ HasWeakHessian u s M σ

/-- **The analytic core** (paper Lemma `lem:o(r²)`, proved in the appendix by mollification):
if `u` is continuous on the open set `s`, has weak gradient `G` and weak Hessian `M dx + σ` on
`s` (and `u ∈ L¹_loc`, which the mollification argument requires), and if `x₀` is a Lebesgue point
of `G` and of `M` at which the singular part has zero density, then the second order Taylor
remainder of `u` at `x₀` is `o(r²)` in `L¹` average. -/
def TaylorCoreInput : Prop :=
  ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (x₀ : ℝ⁴), IsOpen s → x₀ ∈ s → ContinuousOn u s →
  LocallyIntegrable u volume →
  ∀ (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴),
    LocallyIntegrable G volume → (∀ i j, LocallyIntegrable (M i j) volume) →
    HasWeakGradient u s G → HasWeakHessian u s M σ →
    IsLebesguePointVec G x₀ → (∀ i j, IsLebesguePoint (M i j) x₀) →
    (∀ i j, IsVanishingPoint (σ i j).totalVariation x₀) →
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫ y in ball x₀ r, |taylorRemainder u G M x₀ y|) / (volume (ball x₀ r)).toReal
        ≤ ε * r ^ 2

/-- The `2`-convexity of a viscosity solution of `σ₂ = 1` with `Δu ≥ 0`: the subsolution
inequality `G(D²φ) ≥ 0` forces `√(2 + Σλ²) ≤ Σλ` for the eigenvalues of the Hessian of a test
function, hence `σ₂ = ∑_{i<j}λᵢλⱼ ≥ 1 > 0`. -/
theorem isTwoConvexOn_of_viscSolution {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hsol : IsViscSubsolution (fun M => -Gop M) g s) (hΔ : IsViscSubsolution negTrace g s) :
    IsTwoConvexOn g s := by
  refine ⟨hΔ, ?_⟩
  intro φ hφ x hx hloc
  have h1 : 0 ≤ Gop (HessOp φ s x) := by
    have h := hsol φ hφ x hx hloc
    change -Gop (HessOp φ s x) ≤ 0 at h
    linarith
  have hsym : (HessOp φ s x).IsSymmetric :=
    Commons.Analysis.Calculus.FDeriv.isSymmetric_hessianWithin hs hx hφ
  have hfin : Module.finrank ℝ ℝ⁴ = 4 := by simp [finrank_euclideanSpace]
  have htr := Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues hsym
  have haux : LinearMap.trace ℝ ℝ⁴
      ((HessOp φ s x).toLinearMap.adjoint ∘ₗ (HessOp φ s x).toLinearMap)
      = ∑ i : Fin (Module.finrank ℝ ℝ⁴), (hsym.eigenvalues rfl i) ^ 2 := by
    rw [Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq hsym,
      Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq hsym]
  have hge : Real.sqrt (2 + ∑ i : Fin (Module.finrank ℝ ℝ⁴), (hsym.eigenvalues rfl i) ^ 2)
      ≤ ∑ i : Fin (Module.finrank ℝ ℝ⁴), hsym.eigenvalues rfl i := by
    have h2 := h1
    unfold Gop at h2
    rw [htr, haux] at h2
    linarith
  have h3 := Commons.Analysis.Sigma2.pairSum_nonneg_of_sqrt_le_sum_fin hge
  have hσ : σ₂ (HessOp φ s x) = ∑ j : Fin (Module.finrank ℝ ℝ⁴),
      ∑ i : Fin (Module.finrank ℝ ℝ⁴),
        if i < j then hsym.eigenvalues rfl i * hsym.eigenvalues rfl j else 0 := by
    unfold HessianEstimates.σ₂
    rw [dif_pos hsym]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.filter_gt_eq_Iio, Finset.sum_filter]
  show -σ₂ (HessOp φ s x) ≤ 0
  rw [hσ]
  linarith

end Submission
