import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

namespace Work.Sampling

open LeanEval.Analysis.CKMRVInterpolation
open scoped SchwartzMap

/-!
# Continuity and linearity of the CKMRV sampling map

The sampling map `coeffs n k₀` records, for a complex Schwartz function `f` on `R^n`
and every `k ≥ k₀`, the four numbers
`f (r_k)`, `f̂ (r_k)`, `deriv (f ∘ realIncl) r_k`, `deriv (f̂ ∘ realIncl) r_k`,
where `r_k = sqrt (2 * k)` and `f̂` is the Fourier transform of `f`.

This file shows that `coeffs n k₀` is (the underlying function of) a continuous
`ℂ`-linear map. Each of the four entries is a continuous linear functional of `f`:

* evaluation at a point `x` is continuous linear (`evalAtCLM`), since
  `‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f`;
* the radial derivative at `r` is the directional derivative in the direction of the
  unit vector `realIncl 1`, evaluated at `realIncl r` (`derivAtCLM`); by the chain rule
  along the linear curve `realIncl` this is `deriv (g ∘ realIncl) r`;
* the Fourier transform is a continuous linear map (`fourierCLM`).

A map into a product of copies of `ℂ` is continuous linear as soon as all of its
components are, so the four functionals assemble into the required continuous
linear map.
-/

/-- Evaluation of a complex Schwartz function at a point, as a continuous linear
functional. The bound `‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f` makes it continuous. -/
noncomputable def evalAtCLM {n : ℕ} [NeZero n] (x : EuclideanSpace ℝ (Fin n)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x) (by intro f g; rfl) (by intro a f; rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      rw [Finset.sup_singleton, one_mul]
      exact SchwartzMap.norm_le_seminorm ℂ f x⟩

lemma evalAtCLM_apply {n : ℕ} [NeZero n] (x : EuclideanSpace ℝ (Fin n))
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : evalAtCLM x f = f x := rfl

/-- The radial derivative at radius `r`, as a continuous linear functional: it is the
directional derivative in the direction of the unit vector `realIncl 1`, evaluated at
the point `realIncl r`. -/
noncomputable def derivAtCLM {n : ℕ} [NeZero n] (r : ℝ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ :=
  (evalAtCLM (realIncl (n := n) r)) ∘L
    LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) (realIncl (n := n) 1)

/-- `derivAtCLM` computes the ordinary derivative of the restriction of a Schwartz
function to the coordinate axis, by the chain rule along the curve `realIncl`. -/
lemma derivAtCLM_apply {n : ℕ} [NeZero n] (r : ℝ)
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    derivAtCLM r g = deriv (g ∘ realIncl (n := n)) r := by
  rw [derivAtCLM, ContinuousLinearMap.comp_apply, evalAtCLM_apply,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    deriv_comp_realIncl (SchwartzMap.hasFDerivAt g (realIncl (n := n) r))]

/-- The `j`-th sampling functional at the point of index `k`. -/
noncomputable def sampleCLM (n k₀ : ℕ) [NeZero n] (p : Set.Ici k₀ × Fin 4) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ :=
  let r := Real.sqrt (2 * (p.1 : ℝ))
  ![evalAtCLM (realIncl (n := n) r),
    (evalAtCLM (realIncl (n := n) r)) ∘L
      FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
    derivAtCLM (n := n) r,
    (derivAtCLM (n := n) r) ∘L
      FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ))] p.2

/-- **The CKMRV sampling map is continuous linear.** -/
theorem coeffs_continuous_linear (n k₀ : ℕ) [NeZero n] :
    ∃ C : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ((Set.Ici k₀ × Fin 4) → ℂ),
      ∀ f, C f = coeffs n k₀ f := by
  classical
  let L : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ] ((Set.Ici k₀ × Fin 4) → ℂ) :=
    { toFun := fun f p => sampleCLM n k₀ p f
      map_add' := by intro f g; funext p; exact (sampleCLM n k₀ p).map_add f g
      map_smul' := by intro a f; funext p; exact (sampleCLM n k₀ p).map_smul a f }
  have hcont : Continuous L := by
    rw [continuous_pi_iff]
    intro p
    exact (sampleCLM n k₀ p).continuous
  refine ⟨ContinuousLinearMap.mk L hcont, ?_⟩
  intro f
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases j <;>
    simp [L, coeffs, Function.uncurry_apply_pair, sampleCLM, evalAtCLM_apply,
      ContinuousLinearMap.comp_apply, derivAtCLM_apply]

end Work.Sampling
