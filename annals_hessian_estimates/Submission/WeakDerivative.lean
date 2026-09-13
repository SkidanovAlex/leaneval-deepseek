/-
Weak (distributional) gradient and Hessian of a continuous function, and the abstract form of the
paper's Lemma `lem:o(r^2)` of Shankar--Yuan (arXiv:2305.12587), Section 3 / Appendix.

The paper's Proposition 3.1 (Alexandrov regularity) is proved by combining:
* Trudinger's weighted interior gradient estimate for viscosity solutions of `σ₂ = 1` with `Δu > 0`
  (input, `GradientEstimateInput`),
* the fact that the weak Hessian of a 2-convex function is a vector Radon measure
  (Chaudhuri--Trudinger, input, `WeakHessianInput`),
* the two lemmas of the appendix of the paper, `lem:o(r^2)` (mollification) and `lem:pto(r^2)`
  (the latter is already in the commons as
  `Commons.Analysis.MeasureTheory.Lebesgue.sup_le_of_average_and_slope_lt_four`).

This file sets up the notions of weak gradient/weak Hessian and states the analytic core.
-/
import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_const_sub
import Submission.Commons.Measure.WeakDerivative.integral_mul_fderiv_eq_neg_integral_fderiv_mul_of_lipschitzOn

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The `i`-th standard basis vector of `ℝ⁴`. -/
noncomputable def stdE (i : Fin 4) : ℝ⁴ := EuclideanSpace.single i (1 : ℝ)

/-- `u` has **weak gradient** `G` on the open set `s`: for every test function `φ` with support
in `s` and every direction `v`, `∫ u ∂ᵥφ = - ∫ φ ⟪G, v⟫`. -/
def HasWeakGradient (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (G : ℝ⁴ → ℝ⁴) : Prop :=
  ∀ (φ : ℝ⁴ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ s → ∀ v : ℝ⁴,
    ∫ x, u x * (fderiv ℝ φ x) v = - ∫ x, φ x * ⟪G x, v⟫

/-- `u` has **weak Hessian** `M dx + σ` on the open set `s`: for every test function `φ` with
support in `s` and all `i j`,
`∫ u ∂ᵢ∂ⱼφ = ∫ φ Mᵢⱼ + ⟨σᵢⱼ, φ⟩`.  Here `M` is the density of the absolutely continuous part
(with respect to Lebesgue measure) and `σ` the singular part. -/
def HasWeakHessian (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ)
    (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴) : Prop :=
  ∀ (φ : ℝ⁴ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ s → ∀ i j,
    (∫ x, u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j) ∂volume)
      = (∫ x, φ x * M i j x ∂volume) + (∫ᵛ x, φ x ∂•(σ i j))

/-- The notion of weak gradient is insensitive to the values of `u` off `s`: any function agreeing
with `u` on `s` has the same weak gradient on `s`. -/
theorem HasWeakGradient.congr_of_eqOn {u v : ℝ⁴ → ℝ} {s : Set ℝ⁴} {G : ℝ⁴ → ℝ⁴}
    (h : HasWeakGradient u s G) (huv : ∀ x ∈ s, u x = v x) : HasWeakGradient v s G := by
  intro φ hφ hsupp v'
  rw [show (∫ x, v x * (fderiv ℝ φ x) v') = ∫ x, u x * (fderiv ℝ φ x) v' from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show v x * (fderiv ℝ φ x) v' = u x * (fderiv ℝ φ x) v'
      by_cases hx : x ∈ tsupport φ
      · rw [huv x (hsupp hx)]
      · have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
        rw [h0.fderiv_eq]
        simp)]
  exact h φ hφ hsupp v'

/-- The notion of weak Hessian is insensitive to the values of `u` off `s`. -/
theorem HasWeakHessian.congr_of_eqOn {u v : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    {M : Fin 4 → Fin 4 → ℝ⁴ → ℝ} {σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴}
    (h : HasWeakHessian u s M σ) (huv : ∀ x ∈ s, u x = v x) : HasWeakHessian v s M σ := by
  intro φ hφ hsupp i j
  rw [show (∫ x, v x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j) ∂volume)
      = ∫ x, u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j) ∂volume from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show v x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
        = u x * (fderiv ℝ (fderiv ℝ φ) x) (stdE i) (stdE j)
      by_cases hx : x ∈ tsupport φ
      · rw [huv x (hsupp hx)]
      · have h1 : fderiv ℝ φ =ᶠ[𝓝 x] 0 := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
          exact (notMem_tsupport_iff_eventuallyEq.mp hy).fderiv_eq.trans (by simp)
        rw [h1.fderiv_eq]
        simp)]
  exact h φ hφ hsupp i j

/-- A function that is Lipschitz on a **bounded** open set `s` has the a.e. derivative as a weak
gradient on `s`.  (The boundedness is only used to produce compactly supported test functions: on a
bounded `s`, a smooth `φ` with `tsupport φ ⊆ s` has compact support.) -/
theorem HasWeakGradient.of_lipschitzOn {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {C : NNReal} (hs : IsOpen s)
    (hsb : Bornology.IsBounded s) (hu : LipschitzOnWith C u s) :
    HasWeakGradient u s (fun x => (InnerProductSpace.toDual ℝ ℝ⁴).symm (fderiv ℝ u x)) := by
  intro φ hφ hsupp v
  have hcs : HasCompactSupport φ := by
    rw [HasCompactSupport]
    exact Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hsb.subset hsupp⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := Commons.Measure.WeakDerivative.integral_mul_fderiv_eq_neg_integral_fderiv_mul_of_lipschitzOn
    (n := 4) hs hu hsupp hφ1 hcs v
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show φ x * (fderiv ℝ u x) v = φ x * ⟪(InnerProductSpace.toDual ℝ ℝ⁴).symm (fderiv ℝ u x), v⟫_ℝ
  rw [InnerProductSpace.toDual_symm_apply]

/-- `x` is a Lebesgue point of `f` (in the average form used in the paper). -/
def IsLebesguePoint (f : ℝ⁴ → ℝ) (x : ℝ⁴) : Prop :=
  Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x|) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- `x` is a Lebesgue point of the vector valued function `G`. -/
def IsLebesguePointVec (G : ℝ⁴ → ℝ⁴) (x : ℝ⁴) : Prop :=
  Tendsto (fun r : ℝ => ⨍ y in ball x r, ‖G y - G x‖) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The singular part of the weak Hessian has zero density at `x`. -/
def IsVanishingPoint (ρ : Measure ℝ⁴) (x : ℝ⁴) : Prop :=
  Tendsto (fun r : ℝ => (ρ (ball x r)).toReal / r ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The second order Taylor remainder of `u` at `x₀` with linear part `G x₀` and quadratic part
the matrix `M · x₀`. -/
noncomputable def taylorRemainder (u : ℝ⁴ → ℝ) (G : ℝ⁴ → ℝ⁴)
    (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ : ℝ⁴) (y : ℝ⁴) : ℝ :=
  u y - u x₀ - ⟪G x₀, y - x₀⟫
    - (1 / 2) * ∑ i, ∑ j, M i j x₀ * ((y - x₀) i) * ((y - x₀) j)

end Submission
