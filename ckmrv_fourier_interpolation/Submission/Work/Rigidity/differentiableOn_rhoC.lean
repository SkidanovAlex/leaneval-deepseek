import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda

theorem differentiableOn_rhoC :
    DifferentiableOn ℂ Work.Rigidity.rhoC {z : ℂ | 0 < z.im} := by
  have hdlam : DifferentiableOn ℂ (deriv lamC) U :=
    differentiableOn_lamC.deriv isOpen_U
  have hden : DifferentiableOn ℂ
      (fun z : ℂ => lamC z * (1 - lamC z) * (thetaC00 z) ^ 4) U :=
    (differentiableOn_lamC.mul (differentiableOn_lamC.const_sub (1 : ℂ))).mul
      (differentiableOn_thetaC00.pow 4)
  have hne : ∀ z ∈ U, lamC z * (1 - lamC z) * (thetaC00 z) ^ 4 ≠ 0 := by
    intro z hz
    rw [lamC_of_mem hz, thetaC00_of_mem hz]
    exact mul_ne_zero
      (mul_ne_zero (lambdaFun_ne_zero _)
        (sub_ne_zero.mpr (Ne.symm (lambdaFun_ne_one _))))
      (pow_ne_zero 4 (theta00Fun_ne_zero _))
  exact (hdlam.div hden hne).congr (fun z _ => rfl)

end Work.Rigidity
