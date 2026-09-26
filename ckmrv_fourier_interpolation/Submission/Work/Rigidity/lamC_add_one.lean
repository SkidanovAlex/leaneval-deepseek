import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs

namespace Work.Rigidity

open scoped UpperHalfPlane

open Work.Kernels Work.Kernels.LogLambda

/-- `λ_S = 1 - λ` in the extension to `ℂ`: this is Jacobi's quartic identity
`θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴` divided by `θ₀₀⁴`. -/
lemma lamSC_eq_one_sub_lamC (z : ℂ) (hz : 0 < z.im) : lamSC z = 1 - lamC z := by
  have hq : thetaC01 z ^ 4 + thetaC10 z ^ 4 = thetaC00 z ^ 4 := by
    have h := (Work.Kernels.TildeFacts.theta_quartic (⟨z, hz⟩ : ℍ)).symm
    simpa [Work.Kernels.UFun, Work.Kernels.WFun, Work.Kernels.VFun, Work.Kernels.theta00Fun,
      Work.Kernels.theta01Fun, Work.Kernels.theta10Fun, thetaC00, thetaC01, thetaC10] using h
  have hU : thetaC00 z ^ 4 ≠ 0 := pow_ne_zero 4 (thetaC00_ne_zero hz)
  have : thetaC01 z ^ 4 / thetaC00 z ^ 4 + thetaC10 z ^ 4 / thetaC00 z ^ 4 = 1 := by
    rw [← add_div, hq, div_self hU]
  rw [lamSC, lamC, eq_sub_iff_add_eq]
  exact this

theorem lamC_add_one (z : ℂ) (hz : 0 < z.im) :
    Work.Kernels.LogLambda.lamC (z + 1) =
      -(Work.Kernels.LogLambda.lamC z) / (1 - Work.Kernels.LogLambda.lamC z) := by
  rw [Work.Kernels.LogLambda.lamC_add_one hz, lamSC_eq_one_sub_lamC z hz]

end Work.Rigidity
