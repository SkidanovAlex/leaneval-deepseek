import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs

namespace Work.Rigidity

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

/-- The action of `T ^ 2 ∈ SL(2, ℤ)` on `ℍ` is translation by `2` at the level of `ℂ`. -/
private lemma coe_T2_smul (τ : ℍ) :
    (((ModularGroup.T ^ 2 : SL(2, ℤ)) • τ : ℍ) : ℂ) = (τ : ℂ) + 2 := by
  have h1 : (ModularGroup.T ^ 2 : SL(2, ℤ)) • τ = ModularGroup.T • (ModularGroup.T • τ) := by
    rw [pow_two, mul_smul]
  rw [h1]
  have h2 : ((ModularGroup.T • (ModularGroup.T • τ) : ℍ) : ℂ)
      = (1 : ℝ) + ((1 : ℝ) + (τ : ℂ)) := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  rw [h2]; push_cast; ring

theorem periodic_lambdaFun_ofComplex :
    Function.Periodic
      (fun z : ℂ => Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)) 2 := by
  intro z
  change Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex (z + 2))
      = Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)
  by_cases hz : 0 < z.im
  · -- `z` is in the upper half plane: `z + 2` is `T ^ 2 • z` and `λ` is `T ^ 2`-invariant.
    have hz2 : 0 < (z + 2).im := by simpa using hz
    have h1 : UpperHalfPlane.ofComplex (z + 2)
        = (ModularGroup.T ^ 2 : SL(2, ℤ)) • (⟨z, hz⟩ : ℍ) := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz2, UpperHalfPlane.ext_iff]
      exact (coe_T2_smul ⟨z, hz⟩).symm
    have h2 : UpperHalfPlane.ofComplex z = (⟨z, hz⟩ : ℍ) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hz
    rw [h1, h2, lambdaFun_T2]
  · -- `z` is off the upper half plane: `ofComplex` is constant on the lower half plane.
    have hzle : z.im ≤ 0 := not_lt.mp hz
    have hz2 : (z + 2).im ≤ 0 := by simpa using hzle
    rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hz2 hzle]

end Work.Rigidity
