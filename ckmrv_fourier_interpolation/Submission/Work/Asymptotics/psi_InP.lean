import Mathlib
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

/-- `ξ₂ = U + W` and `ξ₄ = U² + W² - 2V²` lie in the class `𝒫` of holomorphic functions of
moderate growth, being polynomials in the fourth powers of Jacobi's theta functions. -/
private lemma xi2_InP : Work.Kernels.InP Work.Kernels.xi2Fun :=
  (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4).add
    (Work.Kernels.InP.pow Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4)

private lemma xi4_InP : Work.Kernels.InP Work.Kernels.xi4Fun :=
  ((Work.Kernels.InP.pow (Work.Kernels.InP.pow
      Work.Kernels.ClassicalFacts.theta00Fun_mem_InP 4) 2).add
    (Work.Kernels.InP.pow (Work.Kernels.InP.pow
      Work.Kernels.ClassicalFacts.theta01Fun_mem_InP 4) 2)).sub
  (Work.Kernels.InP.const_mul 2 (Work.Kernels.InP.pow (Work.Kernels.InP.pow
    Work.Kernels.ClassicalFacts.theta10Fun_mem_InP 4) 2))

/-- The CKMRV basis functions `ψ_2`, `ψ_4` of Proposition 4.3 lie in the class `𝒫` for any
choice of the logarithm data `(𝓛, 𝓛_S)`: each is a sum of two products of a member of `𝒫`
(one of them slashed by `S`) with a member of `𝒫` coming from the data. -/
theorem psi_InP (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.InP (Work.Kernels.psi2 ℓ) ∧ Work.Kernels.InP (Work.Kernels.psi4 ℓ) := by
  have hL : Work.Kernels.InP ℓ.L := ⟨ℓ.holo, ℓ.memP⟩
  have hLS : Work.Kernels.InP ℓ.L_S := ⟨ℓ.holo_S, ℓ.memP_S⟩
  constructor
  · have h : Work.Kernels.psi2 ℓ = fun τ : ℍ => Work.Kernels.xi2Fun τ * ℓ.L τ +
        (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
    rw [h]
    exact (xi2_InP.mul hL).add
      ((Work.Kernels.InP.slash xi2_InP (2 : ℤ) ModularGroup.S).mul hLS)
  · have h : Work.Kernels.psi4 ℓ = fun τ : ℍ => Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
    rw [h]
    exact (xi4_InP.mul hL).add
      ((Work.Kernels.InP.slash xi4_InP (4 : ℤ) ModularGroup.S).mul hLS)

end Work.Asymptotics
