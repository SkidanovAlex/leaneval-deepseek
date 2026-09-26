/-
# The leading term of `λ` at the cusp `i∞`

The modular lambda function is `λ = θ₁₀⁴/θ₀₀⁴` with `q`-expansion at the cusp
`λ(τ) = lambdaSeries (q)`, `q = 𝕢₂ τ = e^{π i τ}`, where

  `lambdaSeries z = 16 z (aSeries z)⁴ / (bSeries z)⁴ = 16 z + O(z²)`

(`Work.Rigidity.lambdaFun_eq_lambdaSeries` for the identity, and
`Work.Rigidity.lambdaSeries_hasStrictDerivAt`, whose derivative is `16 ≠ 0`, for the
expansion).  Dividing by the `q`-parameter therefore gives

  `λ(τ) / 𝕢₂ τ = lambdaSeries q / q ⟶ 16`  as `τ → i∞`  (`⟺ q → 0`).

The two ingredients of the proof are the elementary identity `𝕢₂ z = e^{π i z}` and the
fact that a function with strict derivative `c` at `0` and `f 0 = 0` satisfies
`f z / z → c` along `z → 0`, `z ≠ 0` (the slope of `f` at `0`).
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries
import Submission.Work.Rigidity.lambda_local_surjective

noncomputable section

open UpperHalfPlane Filter Topology

namespace Work.Rigidity

/-- The `q`-parameter of level `2`: `𝕢₂ z = exp (π i z)`. -/
lemma qParam_two_eq (z : ℂ) :
    Function.Periodic.qParam 2 z = Complex.exp (Real.pi * Complex.I * z) := by
  rw [Function.Periodic.qParam]
  congr 1
  push_cast
  ring

/-- The slope of the `q`-expansion of `λ` at the origin tends to its strict derivative `16`. -/
lemma lambdaSeries_div_self_tendsto :
    Tendsto (fun z : ℂ => lambdaSeries z / z) (𝓝[≠] 0) (𝓝 16) := by
  have h := lambdaSeries_hasStrictDerivAt.hasDerivAt.tendsto_slope
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards with z
  simp only [slope, sub_zero, lambdaSeries_zero, sub_zero, smul_eq_mul, vsub_eq_sub,
    div_eq_mul_inv, mul_comm]

/-- **The leading term of `λ` at the cusp.**  `λ(τ)/𝕢₂ τ → 16` as `Im τ → ∞`. -/
theorem lambdaFun_div_qParam_tendsto :
    Filter.Tendsto (fun τ : UpperHalfPlane => Work.Kernels.lambdaFun τ /
      Function.Periodic.qParam 2 (τ : ℂ)) UpperHalfPlane.atImInfty (nhds 16) := by
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam 2 (τ : ℂ)) atImInfty (𝓝[≠] 0) :=
    (Function.Periodic.qParam_tendsto (by norm_num : (0 : ℝ) < 2)).comp
      UpperHalfPlane.tendsto_coe_atImInfty
  have hmain := lambdaSeries_div_self_tendsto.comp hq
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards with τ
  simp only [Function.comp_apply]
  rw [qParam_two_eq, lambdaFun_eq_lambdaSeries τ]

end Work.Rigidity
