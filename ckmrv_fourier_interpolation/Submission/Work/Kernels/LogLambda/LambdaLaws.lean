/-
# The transformation laws of `λ`, `λ_S` and the explicit branch of `log λ_S`

This file records the classical transformation laws of the Hauptmodul `λ = θ₁₀⁴/θ₀₀⁴` and of
`λ_S = 1 - λ = θ₀₁⁴/θ₀₀⁴`:

  `λ(-1/τ) = λ_S(τ)`, `λ_S(-1/τ) = λ(τ)`, `λ(τ+1) = -λ(τ)/λ_S(τ)`, `λ_S(τ+1) = 1/λ_S(τ)`,

first on `ℍ` (from the theta transformation laws of `ThetaLaws`) and then on `ℂ`.  We also
introduce the explicit branch

  `Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)`

of `log λ_S` on the half plane `W = {im z > 1/2}`, mirroring the branch `LU` of `log λ`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

/-! ## Non-vanishing of the theta functions on `ℍ` -/

lemma theta00Fun_ne_zero (τ : ℍ) : theta00Fun τ ≠ 0 :=
  thetaC00_ne_zero τ.im_pos

lemma theta10Fun_ne_zero (τ : ℍ) : theta10Fun τ ≠ 0 :=
  thetaC10_ne_zero τ.im_pos

lemma theta01Fun_ne_zero (τ : ℍ) : theta01Fun τ ≠ 0 := by
  have h : theta01Fun τ = jacobiTheta ((τ : ℂ) + 1) :=
    Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one (τ : ℂ)
  rw [h]
  exact thetaC00_ne_zero (by simpa [Complex.add_im] using τ.im_pos)

/-! ## The transformation laws of `λ` and `λ_S` on `ℍ` -/

lemma lambdaFun_S (τ : ℍ) : lambdaFun (ModularGroup.S • τ) = lambdaSFun τ := by
  have h0 := theta00Fun_S τ
  have h1 := theta10Fun_S τ
  have hne : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (coe_tau_ne_zero τ)
  have hnum : theta10Fun (ModularGroup.S • τ) ^ 4
      = ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 * theta01Fun τ ^ 4 := by
    rw [h1]; ring
  have hden : theta00Fun (ModularGroup.S • τ) ^ 4
      = ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 * theta00Fun τ ^ 4 := by
    rw [h0]; ring
  show theta10Fun (ModularGroup.S • τ) ^ 4 / theta00Fun (ModularGroup.S • τ) ^ 4
      = theta01Fun τ ^ 4 / theta00Fun τ ^ 4
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 4 hne)]

lemma lambdaSFun_S (τ : ℍ) : lambdaSFun (ModularGroup.S • τ) = lambdaFun τ := by
  have h0 := theta00Fun_S τ
  have h1 := theta01Fun_S τ
  have hne : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (coe_tau_ne_zero τ)
  have hnum : theta01Fun (ModularGroup.S • τ) ^ 4
      = ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 * theta10Fun τ ^ 4 := by
    rw [h1]; ring
  have hden : theta00Fun (ModularGroup.S • τ) ^ 4
      = ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 * theta00Fun τ ^ 4 := by
    rw [h0]; ring
  show theta01Fun (ModularGroup.S • τ) ^ 4 / theta00Fun (ModularGroup.S • τ) ^ 4
      = theta10Fun τ ^ 4 / theta00Fun τ ^ 4
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 4 hne)]

lemma lambdaFun_T (τ : ℍ) :
    lambdaFun (ModularGroup.T • τ) = - lambdaFun τ / lambdaSFun τ := by
  have h0 := theta00Fun_T τ
  have h1 := theta10Fun_T τ
  have he4 : (Complex.exp (Real.pi * Complex.I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul]
    rw [show ((4 : ℕ) : ℂ) * (Real.pi * Complex.I / 4) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have h00 : theta00Fun τ ^ 4 ≠ 0 := pow_ne_zero 4 (theta00Fun_ne_zero τ)
  have h01 : theta01Fun τ ^ 4 ≠ 0 := pow_ne_zero 4 (theta01Fun_ne_zero τ)
  show theta10Fun (ModularGroup.T • τ) ^ 4 / theta00Fun (ModularGroup.T • τ) ^ 4
      = - (theta10Fun τ ^ 4 / theta00Fun τ ^ 4) / (theta01Fun τ ^ 4 / theta00Fun τ ^ 4)
  rw [h0, h1]
  rw [show (Complex.exp (Real.pi * Complex.I / 4) * theta10Fun τ) ^ 4
      = - theta10Fun τ ^ 4 by
    rw [mul_pow, he4]; ring]
  simp only [neg_div]
  rw [div_div_div_cancel_right₀ h00]

lemma lambdaSFun_T (τ : ℍ) : lambdaSFun (ModularGroup.T • τ) = (lambdaSFun τ)⁻¹ := by
  have h0 := theta00Fun_T τ
  have h1 := theta01Fun_T τ
  have h00 : theta00Fun τ ^ 4 ≠ 0 := pow_ne_zero 4 (theta00Fun_ne_zero τ)
  have h01 : theta01Fun τ ^ 4 ≠ 0 := pow_ne_zero 4 (theta01Fun_ne_zero τ)
  show theta01Fun (ModularGroup.T • τ) ^ 4 / theta00Fun (ModularGroup.T • τ) ^ 4
      = (theta01Fun τ ^ 4 / theta00Fun τ ^ 4)⁻¹
  rw [h0, h1, inv_div]

/-! ## Consequences at the level of `ℂ` -/

lemma im_neg_inv_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-z⁻¹).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simpa using hz
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

lemma lamC_eq_lamSC_inv {z : ℂ} (hz : 0 < z.im) : lamC z = lamSC (-z⁻¹) := by
  have hzU : 0 < (-z⁻¹).im := im_neg_inv_pos hz
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simpa using hz
  have hS : ModularGroup.S • (⟨-z⁻¹, hzU⟩ : ℍ) = ⟨z, hz⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_S_smul]
    field_simp
  calc lamC z = lambdaFun ⟨z, hz⟩ := rfl
    _ = lambdaFun (ModularGroup.S • ⟨-z⁻¹, hzU⟩) := by rw [hS]
    _ = lambdaSFun ⟨-z⁻¹, hzU⟩ := lambdaFun_S ⟨-z⁻¹, hzU⟩
    _ = lamSC (-z⁻¹) := rfl

lemma lamSC_eq_lamC_inv {z : ℂ} (hz : 0 < z.im) : lamSC z = lamC (-z⁻¹) := by
  have hzU : 0 < (-z⁻¹).im := im_neg_inv_pos hz
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simpa using hz
  have hS : ModularGroup.S • (⟨-z⁻¹, hzU⟩ : ℍ) = ⟨z, hz⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_S_smul]
    field_simp
  calc lamSC z = lambdaSFun ⟨z, hz⟩ := rfl
    _ = lambdaSFun (ModularGroup.S • ⟨-z⁻¹, hzU⟩) := by rw [hS]
    _ = lambdaFun ⟨-z⁻¹, hzU⟩ := lambdaSFun_S ⟨-z⁻¹, hzU⟩
    _ = lamC (-z⁻¹) := rfl

lemma lamC_add_one {z : ℂ} (hz : 0 < z.im) : lamC (z + 1) = -(lamC z) / lamSC z := by
  have hz1 : 0 < (z + 1).im := by simpa [Complex.add_im] using hz
  have hT : ModularGroup.T • (⟨z, hz⟩ : ℍ) = ⟨z + 1, hz1⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_T_smul]
  calc lamC (z + 1) = lambdaFun ⟨z + 1, hz1⟩ := rfl
    _ = lambdaFun (ModularGroup.T • ⟨z, hz⟩) := by rw [hT]
    _ = - lambdaFun ⟨z, hz⟩ / lambdaSFun ⟨z, hz⟩ := lambdaFun_T ⟨z, hz⟩
    _ = -(lamC z) / lamSC z := rfl

lemma lamSC_add_one {z : ℂ} (hz : 0 < z.im) : lamSC (z + 1) = (lamSC z)⁻¹ := by
  have hz1 : 0 < (z + 1).im := by simpa [Complex.add_im] using hz
  have hT : ModularGroup.T • (⟨z, hz⟩ : ℍ) = ⟨z + 1, hz1⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_T_smul]
  calc lamSC (z + 1) = lambdaSFun ⟨z + 1, hz1⟩ := rfl
    _ = lambdaSFun (ModularGroup.T • ⟨z, hz⟩) := by rw [hT]
    _ = (lambdaSFun ⟨z, hz⟩)⁻¹ := lambdaSFun_T ⟨z, hz⟩
    _ = (lamSC z)⁻¹ := rfl

/-! ## The explicit branch `Λ_S` of `log λ_S` on `W` -/

/-- The explicit branch `Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)` of `log λ_S` on `{im z > 1/2}`. -/
def LamS (z : ℂ) : ℂ := 4 * Complex.log (thetaC01 z) - 4 * Complex.log (thetaC00 z)

lemma thetaC01_mem_slitPlane_W {z : ℂ} (hz : 1 / 2 < z.im) : thetaC01 z ∈ Complex.slitPlane := by
  rw [thetaC01, Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one]
  exact thetaC00_mem_slitPlane_W (by simpa [Complex.add_im] using hz)

lemma thetaC01_ne_zero_W {z : ℂ} (hz : 1 / 2 < z.im) : thetaC01 z ≠ 0 := by
  rw [thetaC01, Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one]
  exact thetaC00_ne_zero_W (by simpa [Complex.add_im] using hz)

lemma exp_LamS_W (z : ℂ) (hz : 1 / 2 < z.im) : Complex.exp (LamS z) = lamSC z := by
  have h1 : thetaC01 z ≠ 0 := thetaC01_ne_zero_W hz
  have h0 : thetaC00 z ≠ 0 := thetaC00_ne_zero_W hz
  have hmain : Complex.exp (LamS z) = (thetaC01 z) ^ 4 * ((thetaC00 z) ^ 4)⁻¹ := by
    rw [LamS]
    rw [show (4 : ℂ) * Complex.log (thetaC01 z) - 4 * Complex.log (thetaC00 z)
        = (4 : ℂ) * Complex.log (thetaC01 z) + (-4) * Complex.log (thetaC00 z) by ring]
    rw [Complex.exp_add, exp_four_log h1, exp_neg_four_log h0]
  rw [hmain, lamSC, div_eq_mul_inv]

lemma continuousOn_LamS_W : ContinuousOn LamS W := by
  have h1 : ContinuousOn (fun z : ℂ => 4 * Complex.log (thetaC01 z)) W :=
    (((differentiableOn_thetaC01.mono W_subset_U).continuousOn).clog
      (fun z hz => thetaC01_mem_slitPlane_W hz)).const_mul 4
  have h2 : ContinuousOn (fun z : ℂ => 4 * Complex.log (thetaC00 z)) W :=
    (((differentiableOn_thetaC00.mono W_subset_U).continuousOn).clog
      (fun z hz => thetaC00_mem_slitPlane_W hz)).const_mul 4
  exact h1.sub h2

lemma differentiableOn_LamS_W : DifferentiableOn ℂ LamS W := by
  have h1 : DifferentiableOn ℂ (fun z : ℂ => 4 * Complex.log (thetaC01 z)) W :=
    ((differentiableOn_thetaC01.mono W_subset_U).clog
      (fun z hz => thetaC01_mem_slitPlane_W hz)).const_mul 4
  have h2 : DifferentiableOn ℂ (fun z : ℂ => 4 * Complex.log (thetaC00 z)) W :=
    ((differentiableOn_thetaC00.mono W_subset_U).clog
      (fun z hz => thetaC00_mem_slitPlane_W hz)).const_mul 4
  exact h1.sub h2

end Work.Kernels.LogLambda
