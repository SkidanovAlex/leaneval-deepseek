/-
# The functional equations of `K_+` in group-algebra form

This file bridges the explicit pointwise functional equations of `Work.Kernels.T2op` and
`Work.Kernels.Sop` (proved in `PhiAnnihilation.lean` and `KernelFacts/`) to the group-algebra
form used in CKMRV Theorem 4.9(2): `K_+ |^τ_{d/2} r = 0` for `r ∈ 𝓘₊`.
-/
import Mathlib
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.AlgebraFacts.slash_mul
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

lemma slash_R_T (k : ℤ) (F : ℍ → ℂ) : slash k R_T F = F ∣[k] ModularGroup.T := by
  simp [slash, R_T, MonoidAlgebra.coeff_single]

lemma slash_R_S (k : ℤ) (F : ℍ → ℂ) : slash k R_S F = F ∣[k] ModularGroup.S := by
  simp [slash, R_S, MonoidAlgebra.coeff_single]

lemma slash_neg (k : ℤ) (r : R) (F : ℍ → ℂ) : slash k (-r) F = - slash k r F := by
  have h1 : slash k (-r) F + slash k r F = 0 := by
    rw [← slash_add, neg_add_cancel, slash_zero]
  exact eq_neg_of_add_eq_zero_left h1

lemma slash_sub (k : ℤ) (r s : R) (F : ℍ → ℂ) :
    slash k (r - s) F = slash k r F - slash k s F := by
  rw [sub_eq_add_neg, slash_add, slash_neg, sub_eq_add_neg]

lemma denom_T (z : ℂ) : UpperHalfPlane.denom (glOf ModularGroup.T) z = 1 := by
  show (glOf ModularGroup.T) 1 0 * z + (glOf ModularGroup.T) 1 1 = 1
  rw [glOf_apply, glOf_apply]
  have h1 : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by decide
  have h0 : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by decide
  rw [h1, h0]; norm_num

lemma slash_T_apply (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.T) τ = F ((1 : ℝ) +ᵥ τ) := by
  rw [SL_slash_apply, denom_T]
  have hT : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)
  rw [hT]
  simp

lemma denom_glOf (γ : SL(2,ℤ)) (z : ℂ) :
    UpperHalfPlane.denom (glOf γ) z = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
  show (glOf γ) 1 0 * z + (glOf γ) 1 1 = _
  rw [glOf_apply, glOf_apply]
  push_cast
  ring

lemma slash_R_T_sq (k : ℤ) (F : ℍ → ℂ) :
    slash k (R_T * R_T) F = fun τ => F ((2 : ℝ) +ᵥ τ) := by
  rw [AlgebraFacts.slash_mul, slash_R_T, slash_R_T, ← SlashAction.slash_mul]
  ext τ
  rw [SL_slash_apply]
  have hT2 : (ModularGroup.T * ModularGroup.T) • τ = (2 : ℝ) +ᵥ τ := by
    rw [← pow_two]
    exact UpperHalfPlane.modular_T_zpow_smul τ 2
  rw [hT2, denom_glOf]
  have h1 : ((ModularGroup.T * ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    decide
  have h0 : ((ModularGroup.T * ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    decide
  rw [h1, h0]
  norm_num

lemma slash_T2 (k : ℤ) (F : ℍ → ℂ) : slash k ((R_T - 1) ^ 2) F = T2op F := by
  have hexp : (R_T - 1) ^ 2 = R_T * R_T - (R_T + R_T) + 1 := by noncomm_ring
  rw [hexp, slash_add, slash_sub, slash_add, slash_R_T_sq, slash_R_T, slash_one]
  ext τ
  simp only [T2op, Pi.sub_apply, Pi.add_apply, slash_T_apply]
  ring

lemma slash_S_add_op (k : ℤ) (F : ℍ → ℂ) : slash k (R_S + 1) F = Sop k F := by
  rw [slash_add, slash_R_S, slash_one]
  ext τ
  simp [Sop]

lemma slash_S_sub_op (k : ℤ) (F : ℍ → ℂ) : slash k (R_S - 1) F = Sopm k F := by
  rw [sub_eq_add_neg, slash_add, slash_neg, slash_R_S, slash_one]
  ext τ
  simp only [Sopm, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

/-- `K_+^{(d)}` is annihilated by `(T-I)²` in the `τ` variable at weight `d/2`. -/
theorem KPlus_slash_T2 (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) ((R_T - 1) ^ 2) (fun τ => KPlus d τ z) = 0 := by
  rw [slash_T2]
  exact KernelFacts.KPlus_T2 d hd z

/-- `K_+^{(d)}` is annihilated by `S+I` in the `τ` variable at weight `d/2`. -/
theorem KPlus_slash_S_add (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    slash ((d : ℤ) / 2) (R_S + 1) (fun τ => KPlus d τ z) = 0 := by
  rw [slash_S_add_op]
  exact KernelFacts.KPlus_S_add d hd z

end Work.Kernels
