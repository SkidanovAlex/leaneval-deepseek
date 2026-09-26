import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs

namespace Work.Rigidity

/-- The classical `S`-transformation law `λ(-1/τ) = 1 - λ(τ)` of the modular lambda function,
for the extension `lamC` of `λ` to the upper half plane `{0 < im z}`.

Since `lamSC z = λ_S(z) = 1 - λ(z) = 1 - lamC z` by the quartic theta identity
`θ₁₀⁴ + θ₀₁⁴ = θ₀₀⁴`, and `lamSC z = lamC (-z⁻¹)` by the `S`-law of `θ₀₁`/`θ₁₀`,
this is exactly `lamC (-1/z) = 1 - lamC z`. -/
theorem lamC_neg_inv (z : ℂ) (hz : 0 < z.im) :
    Work.Kernels.LogLambda.lamC (-1 / z) = 1 - Work.Kernels.LogLambda.lamC z := by
  have hneg : (-1 : ℂ) / z = -z⁻¹ := by rw [neg_div, one_div]
  rw [hneg, ← Work.Kernels.LogLambda.lamSC_eq_lamC_inv hz,
      Work.Kernels.LogLambda.lamSC_of_mem hz, Work.Kernels.LogLambda.lamC_of_mem hz]
  have h := Work.Rigidity.lambdaFun_add_lambdaSFun ⟨z, hz⟩
  rw [← h]; ring

end Work.Rigidity
