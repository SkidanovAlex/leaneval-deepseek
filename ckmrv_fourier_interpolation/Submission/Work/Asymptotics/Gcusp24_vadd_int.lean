import Mathlib
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.KernelFacts.KPlus_T2

namespace Work.Asymptotics

/-- **The affine law of the `i = 1` coefficients of the dimension-24 cusp expansion.**
Along the `T`-translation `τ ↦ τ + n` the two coefficient functions `G_{1,0}`, `G_{1,1}` of
`Work.Asymptotics.Gcusp24` are affine in `n`. -/
theorem Gcusp24_vadd_int (ℓ : Work.Kernels.LogLambdaData) (j : Fin 2) (τ : UpperHalfPlane)
    (n : ℤ) :
    Work.Asymptotics.Gcusp24 ℓ 1 j ((n : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 j τ
        + (n : ℂ) * (Work.Asymptotics.Gcusp24 ℓ 1 j ((1 : ℝ) +ᵥ τ)
            - Work.Asymptotics.Gcusp24 ℓ 1 j τ) := by
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with hj | hj
  · -- `j = 0`: the affine law of the first component, `Work.Asymptotics.Gcusp10_vadd_int`.
    rw [hj]
    exact Gcusp10_vadd_int ℓ n τ
  · -- `j = 1`: `G_{1,1} = (i/3456) F24` and `F24(τ+n) = F24 τ - 2πi n 𝔸 τ`.
    rw [hj]
    rw [Gcusp24_one_one ℓ ((n : ℝ) +ᵥ τ), Gcusp24_one_one ℓ ((1 : ℝ) +ᵥ τ),
      Gcusp24_one_one ℓ τ]
    rw [F24_vadd_int n τ, F24_vadd_one τ]
    ring

end Work.Asymptotics
