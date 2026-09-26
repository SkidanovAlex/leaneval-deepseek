/-
# The norm of the theta vector is a `SL(2,ℤ)`-equivariant line bundle section

The three Jacobi theta functions `θ₀₀, θ₀₁, θ₁₀` (the components of `thetaVec`) satisfy,
under the action of `SL(2,ℤ)` on the upper half plane, the transformation laws

  `θ_j(γ • τ) = (permutation of the indices) · j(γ,τ)^{1/2} · θ_{σ(j)}(τ)`,

with `j(γ,τ) = cτ + d` the usual factor of automorphy.  Taking absolute values, the vector
of norms `τ ↦ (‖θ₀₀ τ‖, ‖θ₀₁ τ‖, ‖θ₁₀ τ‖)` is permuted by `γ` and scaled by `‖j(γ,τ)‖^{1/2}`.

The transformation is proved here for all of `SL(2,ℤ)` by checking the two generators `S`
and `T` (whose laws are in `ThetaLaws`), observing that the property is preserved by products
and inverses — the key inputs being the cocycle `j(γ₁γ₂,τ) = j(γ₁,γ₂τ) j(γ₂,τ)` and the
absolute convergence/non-vanishing encoded in `thetaVec` — and finally invoking
`SpecialLinearGroup.SL2Z_generators`.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.SlashDefs

namespace Work.Kernels.LogLambda.ThetaLower

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

/-- The proposition that `γ` permutes the theta components and scales their norms by
`‖j(γ,τ)‖^{1/2}`. -/
noncomputable def thetaNormLaw (γ : SL(2,ℤ)) : Prop :=
  ∃ σ : Fin 3 ≃ Fin 3, ∀ (τ : ℍ) (k : Fin 3),
    ‖thetaVec (σ k) (γ • τ)‖
      = ‖jFun γ (τ : ℂ)‖ ^ (1/2 : ℝ) * ‖thetaVec k τ‖

/-- `j(1, z) = 1`. -/
lemma jFun_one_apply (z : ℂ) : jFun 1 z = 1 := by
  rw [jFun_apply]; simp

/-- The cocycle identity for the factor of automorphy:
`j(γ₁γ₂, τ) = j(γ₁, γ₂ • τ) · j(γ₂, τ)`. -/
lemma jFun_mul_cocycle (γ₁ γ₂ : SL(2,ℤ)) (τ : ℍ) :
    jFun (γ₁ * γ₂) (τ : ℂ) = jFun γ₁ (((γ₂ • τ : ℍ) : ℂ)) * jFun γ₂ (τ : ℂ) := by
  have hdet : 0 < (glOf γ₂).det.val := by
    have h2 : (glOf γ₂).det.val = 1 := by
      have h3 : (glOf γ₂).det = 1 := by
        simp only [glOf]; exact SpecialLinearGroup.coeToGL_det _
      rw [h3]; rfl
    rw [h2]; norm_num
  rw [jFun, show glOf (γ₁ * γ₂) = glOf γ₁ * glOf γ₂ from by
        simp only [glOf, map_mul]]
  rw [UpperHalfPlane.denom_cocycle (glOf γ₁) (glOf γ₂) τ.im_ne_zero]
  rw [← UpperHalfPlane.coe_smul_of_det_pos hdet τ, jFun, jFun]
  congr 1

/-- `‖(-iτ)^{1/2}‖ = ‖τ‖^{1/2}`. -/
lemma norm_cpow_half (τ : ℍ) :
    ‖(-Complex.I * (τ : ℂ)) ^ (1/2 : ℂ)‖ = ‖(τ : ℂ)‖ ^ (1/2 : ℝ) := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
  congr 1
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- `‖exp (π i / 4)‖ = 1`. -/
lemma norm_exp_piI_div_four : ‖Complex.exp (Real.pi * Complex.I / 4)‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma thetaNormLaw_one : thetaNormLaw 1 := by
  refine ⟨Equiv.refl _, ?_⟩
  intro τ k
  simp only [Equiv.refl_apply, one_smul]
  rw [jFun_one_apply, norm_one, Real.one_rpow, one_mul]

lemma thetaNormLaw_S : thetaNormLaw S := by
  refine ⟨Equiv.swap 1 2, ?_⟩
  intro τ k
  have hτ : jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [jFun_apply, ModularGroup.coe_S]; simp
  rw [hτ]
  fin_cases k
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 1 2 (0 : Fin 3) = 0 from by decide]
    simp only [thetaVec_zero]
    rw [theta00Fun_S, norm_mul, norm_cpow_half]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 1 2 (1 : Fin 3) = 2 from by decide]
    simp only [thetaVec_one, thetaVec_two]
    rw [theta10Fun_S, norm_mul, norm_cpow_half]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 1 2 (2 : Fin 3) = 1 from by decide]
    simp only [thetaVec_two, thetaVec_one]
    rw [theta01Fun_S, norm_mul, norm_cpow_half]

lemma thetaNormLaw_T : thetaNormLaw T := by
  refine ⟨Equiv.swap 0 1, ?_⟩
  intro τ k
  have hτ : jFun ModularGroup.T (τ : ℂ) = 1 := by
    rw [jFun_apply, ModularGroup.coe_T]; simp
  rw [hτ, norm_one, Real.one_rpow, one_mul]
  fin_cases k
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 0 1 (0 : Fin 3) = 1 from by decide]
    simp only [thetaVec_zero, thetaVec_one]
    rw [theta01Fun_T]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 0 1 (1 : Fin 3) = 0 from by decide]
    simp only [thetaVec_one, thetaVec_zero]
    rw [theta00Fun_T]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [show Equiv.swap 0 1 (2 : Fin 3) = 2 from by decide]
    simp only [thetaVec_two]
    rw [theta10Fun_T, norm_mul, norm_exp_piI_div_four, one_mul]

lemma thetaNormLaw_mul {γ₁ γ₂ : SL(2,ℤ)} (h₁ : thetaNormLaw γ₁) (h₂ : thetaNormLaw γ₂) :
    thetaNormLaw (γ₁ * γ₂) := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  refine ⟨σ₂.trans σ₁, ?_⟩
  intro τ k
  have hcoc : ‖jFun (γ₁ * γ₂) (τ : ℂ)‖
      = ‖jFun γ₁ (((γ₂ • τ : ℍ) : ℂ))‖ * ‖jFun γ₂ (τ : ℂ)‖ := by
    rw [jFun_mul_cocycle, norm_mul]
  rw [mul_smul, Equiv.trans_apply, hσ₁ (γ₂ • τ) (σ₂ k), hσ₂ τ k, hcoc,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  ring

lemma thetaNormLaw_inv {γ : SL(2,ℤ)} (h : thetaNormLaw γ) : thetaNormLaw γ⁻¹ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, ?_⟩
  intro τ k
  have key := hσ (γ⁻¹ • τ) (σ.symm k)
  simp only [Equiv.apply_symm_apply] at key
  rw [show γ • (γ⁻¹ • τ) = τ from by rw [← mul_smul, mul_inv_cancel, one_smul]] at key
  have hdc : ‖jFun γ⁻¹ (τ : ℂ)‖ ^ (1/2 : ℝ) * ‖jFun γ (((γ⁻¹ • τ : ℍ) : ℂ))‖ ^ (1/2 : ℝ) = 1 := by
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    have h1 : ‖jFun γ⁻¹ (τ : ℂ)‖ * ‖jFun γ (((γ⁻¹ • τ : ℍ) : ℂ))‖ = 1 := by
      rw [mul_comm, ← norm_mul, ← jFun_mul_cocycle γ γ⁻¹ τ, mul_inv_cancel, jFun_one_apply,
        norm_one]
    rw [h1, Real.one_rpow]
  rw [key, ← mul_assoc, hdc, one_mul]

theorem theta_smul_SL2 (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ σ : Fin 3 ≃ Fin 3, ∀ (τ : UpperHalfPlane) (k : Fin 3),
      ‖Work.Kernels.thetaVec (σ k) (γ • τ)‖
        = ‖Work.Kernels.jFun γ (τ : ℂ)‖ ^ (1/2 : ℝ) * ‖Work.Kernels.thetaVec k τ‖ := by
  have hgen : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2,ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  exact Subgroup.closure_induction (p := fun g _ => thetaNormLaw g)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact thetaNormLaw_S
      · exact thetaNormLaw_T)
    thetaNormLaw_one
    (fun x y _ _ hx hy => thetaNormLaw_mul hx hy)
    (fun x _ hx => thetaNormLaw_inv hx)
    hgen

end Work.Kernels.LogLambda.ThetaLower
