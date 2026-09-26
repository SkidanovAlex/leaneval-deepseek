import Mathlib
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.PhiAnnihilation

namespace Work.Kernels.KernelFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-! ## `T`-invariance of the basic modular forms and of `fk`, `PiMat` -/

lemma E4Fun_vadd_one (τ : ℍ) : Work.Kernels.E4Fun ((1:ℝ)+ᵥτ) = Work.Kernels.E4Fun τ := by
  have hT : (ModularGroup.T : SL(2,ℤ)) • τ = (1:ℝ)+ᵥτ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1:ℤ)
  rw [← hT]
  have hγ : ((ModularGroup.T : SL(2,ℤ)) : GL (Fin 2) ℝ) ∈
      (SpecialLinearGroup.mapGL ℝ).range := ⟨(ModularGroup.T : SL(2,ℤ)), rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'
    (F := ModularForm (SpecialLinearGroup.mapGL ℝ).range 4) ModularForm.E₄ hγ τ
  simpa using h

lemma E6Fun_vadd_one (τ : ℍ) : Work.Kernels.E6Fun ((1:ℝ)+ᵥτ) = Work.Kernels.E6Fun τ := by
  have hT : (ModularGroup.T : SL(2,ℤ)) • τ = (1:ℝ)+ᵥτ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1:ℤ)
  rw [← hT]
  have hγ : ((ModularGroup.T : SL(2,ℤ)) : GL (Fin 2) ℝ) ∈
      (SpecialLinearGroup.mapGL ℝ).range := ⟨(ModularGroup.T : SL(2,ℤ)), rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'
    (F := ModularForm (SpecialLinearGroup.mapGL ℝ).range 6) ModularForm.E₆ hγ τ
  simpa using h

lemma DeltaFun_vadd_one (τ : ℍ) : Work.Kernels.DeltaFun ((1:ℝ)+ᵥτ) = Work.Kernels.DeltaFun τ := by
  have hT : (ModularGroup.T : SL(2,ℤ)) • τ = (1:ℝ)+ᵥτ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1:ℤ)
  rw [← hT]
  have hγ : ((ModularGroup.T : SL(2,ℤ)) : GL (Fin 2) ℝ) ∈
      (SpecialLinearGroup.mapGL ℝ).range := ⟨(ModularGroup.T : SL(2,ℤ)), rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'
    (F := CuspForm (SpecialLinearGroup.mapGL ℝ).range 12) CuspForm.discriminant hγ τ
  simpa using h

lemma E8Fun_vadd_one (τ : ℍ) : Work.Kernels.E8Fun ((1:ℝ)+ᵥτ) = Work.Kernels.E8Fun τ := by
  simp only [Work.Kernels.E8Fun, E4Fun_vadd_one]

lemma E10Fun_vadd_one (τ : ℍ) : Work.Kernels.E10Fun ((1:ℝ)+ᵥτ) = Work.Kernels.E10Fun τ := by
  simp only [Work.Kernels.E10Fun, E4Fun_vadd_one, E6Fun_vadd_one]

lemma E14Fun_vadd_one (τ : ℍ) : Work.Kernels.E14Fun ((1:ℝ)+ᵥτ) = Work.Kernels.E14Fun τ := by
  simp only [Work.Kernels.E14Fun, E4Fun_vadd_one, E6Fun_vadd_one]

lemma jInvariantFun_vadd_one (τ : ℍ) :
    Work.Kernels.jInvariantFun ((1:ℝ)+ᵥτ) = Work.Kernels.jInvariantFun τ := by
  simp only [Work.Kernels.jInvariantFun, E4Fun_vadd_one, DeltaFun_vadd_one]

lemma fk_vadd_one (k : ℤ) (τ : ℍ) : Work.Kernels.fk k ((1:ℝ)+ᵥτ) = Work.Kernels.fk k τ := by
  unfold Work.Kernels.fk
  split_ifs <;>
    simp only [E4Fun_vadd_one, E6Fun_vadd_one, E8Fun_vadd_one, E10Fun_vadd_one,
      E14Fun_vadd_one, DeltaFun_vadd_one]

lemma PiMat_vadd_one (v : Fin 3 → ℤ) (τ : ℍ) :
    Work.Kernels.PiMat v ((1:ℝ)+ᵥτ) = Work.Kernels.PiMat v τ := by
  unfold Work.Kernels.PiMat
  simp only [fk_vadd_one]

/-! ## `T`-invariance of the coefficient matrix `Υ_+` -/

lemma UpsilonPlus_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    Work.Kernels.UpsilonPlus d ((1:ℝ)+ᵥτ) z i j = Work.Kernels.UpsilonPlus d τ z i j := by
  simp only [Work.Kernels.UpsilonPlus]
  split_ifs with h8 h24 <;>
    simp only [PiMat_vadd_one, jInvariantFun_vadd_one]

/-! ## `T`-invariance of the coefficient function, and the main theorem -/

lemma KPlusCoeff_vadd_one (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) :
    Work.Kernels.KPlusCoeff d z i ((1:ℝ)+ᵥτ) = Work.Kernels.KPlusCoeff d z i τ := by
  unfold Work.Kernels.KPlusCoeff
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [UpsilonPlus_vadd_one]

lemma phiVec_T2 (i : Fin 3) : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ i) = 0 := by
  fin_cases i
  · simp only [Work.Kernels.phiVec]; exact Work.Kernels.phiNeg2_T2
  · simp only [Work.Kernels.phiVec]; exact Work.Kernels.phi0_T2
  · simp only [Work.Kernels.phiVec]; exact Work.Kernels.phi2_T2

theorem KPlus_T2 (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.T2op (fun τ : UpperHalfPlane => Work.Kernels.KPlus d τ z) = 0 := by
  have _ := hd
  have h1 : (fun τ : ℍ => Work.Kernels.KPlus d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => Work.Kernels.phiVec τ i *
          Work.Kernels.KPlusCoeff d z i τ) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Work.Kernels.KPlus_eq_sum d τ z
  rw [h1]
  refine Work.Kernels.T2op_sum Finset.univ (fun i _ => ?_)
  refine Work.Kernels.T2op_mul_of (phiVec_T2 i) (fun τ => KPlusCoeff_vadd_one d z i τ)

end Work.Kernels.KernelFacts
