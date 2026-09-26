/-
# Assembly of the logarithm data `(𝓛, 𝓛_S)` of CKMRV

Taking `𝓛 = Lfun` (the normalised logarithm of `λ`, see `LogExtension`, `LogNormalisation`,
`LogLaws`) and `𝓛_S(z) = Lfun(-z⁻¹)`, the four transformation laws (2.9) of CKMRV hold, and
`𝓛` has moderate growth.  This file assembles the fields of `Work.Kernels.LogLambdaData`,
leaving the moderate growth of `𝓛` as a hypothesis (`Lfun_growth_of_bounds` discharges it).
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LogNormalisation
import Submission.Work.Kernels.LogLambda.LogLaws

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.LogLambda

/-- The slash of `Lfun` by `S` is `z ↦ Lfun(-z⁻¹)`. -/
theorem Lfun_slash_S :
    (fun τ : ℍ => Lfun (τ : ℂ)) ∣[(0 : ℤ)] ModularGroup.S
      = fun τ : ℍ => Lfun (-(τ : ℂ)⁻¹) := by
  funext τ
  rw [slash_apply', coe_S_smul]
  simp

/-- `Nonempty LogLambdaData`, given moderate growth of `Lfun`. -/
theorem logLambdaData_of
    (hMemP : Work.Kernels.ModerateGrowthOn Set.univ (fun τ : ℍ => Lfun (τ : ℂ))) :
    Nonempty Work.Kernels.LogLambdaData := by
  have hholo : MDiff (fun τ : ℍ => Lfun (τ : ℂ)) := by
    intro τ
    exact MDifferentiableAt.comp τ
      (DifferentiableAt.mdifferentiableAt
        ((Lfun_spec.1 (τ : ℂ) τ.2).differentiableAt (isOpen_U.mem_nhds τ.2)))
      τ.mdifferentiable_coe
  have hholoS : MDiff (fun τ : ℍ => Lfun (-(τ : ℂ)⁻¹)) := by
    intro τ
    have hne : (τ : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.im h
      simp only [Complex.zero_im, UpperHalfPlane.coe_im] at this
      exact absurd this (ne_of_gt τ.im_pos)
    have hmem : -(τ : ℂ)⁻¹ ∈ U := im_neg_inv_pos τ.im_pos
    have h2 : DifferentiableAt ℂ (fun z : ℂ => -z⁻¹) (τ : ℂ) := (differentiableAt_inv hne).neg
    exact MDifferentiableAt.comp τ
      (DifferentiableAt.mdifferentiableAt
        ((Lfun_spec.1 (-(τ : ℂ)⁻¹) hmem).differentiableAt (isOpen_U.mem_nhds hmem)))
      (h2.mdifferentiableAt.comp τ τ.mdifferentiable_coe)
  have hmemPS : Work.Kernels.ModerateGrowthOn Set.univ (fun τ : ℍ => Lfun (-(τ : ℂ)⁻¹)) := by
    have h := Work.Kernels.moderateGrowthOn_slash hMemP (0 : ℤ) ModularGroup.S
    rw [Lfun_slash_S] at h
    simpa using h
  refine ⟨{ L := fun τ : ℍ => Lfun (τ : ℂ)
            L_S := fun τ : ℍ => Lfun (-(τ : ℂ)⁻¹)
            holo := hholo
            holo_S := hholoS
            memP := hMemP
            memP_S := hmemPS
            exp_L := fun τ => Lfun_spec.2.1 (τ : ℂ) τ.2
            exp_L_S := fun τ => ?_
            slash_T := fun τ => ?_
            slash_T_S := fun τ => ?_
            slash_S := Lfun_slash_S
            slash_S_S := ?_ }⟩
  · have hmem : -(τ : ℂ)⁻¹ ∈ U := im_neg_inv_pos τ.im_pos
    have h1 : lamSC (↑τ) = lambdaSFun ⟨(τ : ℂ), τ.2⟩ := rfl
    have h2 : (⟨(τ : ℂ), τ.2⟩ : ℍ) = τ := rfl
    rw [Lfun_spec.2.1 _ hmem, ← lamSC_eq_lamC_inv τ.im_pos, h1, h2]
  · rw [slash_apply', coe_T_smul]
    simp only [neg_zero, zpow_zero, mul_one]
    exact lfun_add_one (τ : ℂ) τ.2
  · rw [slash_apply', coe_T_smul]
    simp only [neg_zero, zpow_zero, mul_one]
    exact lfun_inv_add_one (τ : ℂ) τ.2
  · funext τ
    rw [slash_apply', coe_S_smul]
    simp only [neg_zero, zpow_zero, mul_one]
    congr 1
    field_simp

end Work.Kernels.LogLambda
