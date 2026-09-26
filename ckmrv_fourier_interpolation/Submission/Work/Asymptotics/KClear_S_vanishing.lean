import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.All
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.KMinusCuspBallDefs

namespace Work.Asymptotics

open Work.Kernels UpperHalfPlane ModularForm Matrix
open scoped MatrixGroups ModularForm

/-! ## The transformation laws of the cleared coefficients under `τ ↦ S•τ`

Since `j(S•τ) = j(τ)`, the middle matrix of `Υ_±^{clear}` is *literally* the same at `S•τ`
as at `τ`; only the outer diagonal factors `Π^Δ` change, and they change by the diagonal
matrix of the weights `12 + v_i` (`Δ` has weight `12` and `f_{v_i}` has weight `v_i`).  Its
entries are therefore `τ^{12 + v_i}` times the entries at `τ`.

The proofs are immediate from the modularity of the `f_k` and of `Δ`
(`Work.Kernels.KernelFacts.fk_S_smul`, `Work.Kernels.KernelFacts.DeltaFun_S_slash`) and the
`S`-invariance of the `j`-invariant (`Work.Kernels.KernelFacts.jInvariantFun_S_smul`). -/

/-- The entries of `Π^Δ_a(τ)·M·Π_b(z)` as a three-fold product. -/
private lemma PiMatDelta_mul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : ℍ) (i j : Fin 3) :
    (PiMatDelta a τ * M * PiMat b z) i j =
      (DeltaFun τ * fk (a i) τ) * M i j * fk (b j) z := by
  simp only [PiMatDelta, PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The entries of `Π^Δ_a(τ)·M·(c • Π_b(z))` as a three-fold product. -/
private lemma PiMatDelta_mul_smul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : ℂ) (τ z : ℍ) (i j : Fin 3) :
    (PiMatDelta a τ * M * (c • PiMat b z)) i j
      = (DeltaFun τ * fk (a i) τ) * M i j * (c * fk (b j) z) := by
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  simp only [PiMatDelta, PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- The coordinates of an element of `ℍ` are non-zero. -/
private lemma tau_ne_zero' (τ : ℍ) : (τ : ℂ) ≠ 0 :=
  fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im τ, h]; simp)

private lemma UpsilonPlusClear_S_8 (z τ : ℍ) (i j : Fin 3) :
    UpsilonPlusClear 8 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![6,4,2] : Fin 3 → ℤ) i)) * UpsilonPlusClear 8 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
    KernelFacts.jInvariantFun_S_smul τ
  have hΔ : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ (12 : ℤ) * DeltaFun τ :=
    KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ
  have hfk : fk ((![6,4,2] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![6,4,2] : Fin 3 → ℤ) i) * fk ((![6,4,2] : Fin 3 → ℤ) i) τ :=
    KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [UpsilonPlusClear, reduceIte, Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_PiMat_entry, PiMatDelta_mul_PiMat_entry, hΔ, hfk]
  rw [zpow_add₀ hτ]
  ring

private lemma UpsilonPlusClear_S_24 (z τ : ℍ) (i j : Fin 3) :
    UpsilonPlusClear 24 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![14,12,10] : Fin 3 → ℤ) i)) * UpsilonPlusClear 24 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
    KernelFacts.jInvariantFun_S_smul τ
  have hΔ : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ (12 : ℤ) * DeltaFun τ :=
    KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ
  have hfk : fk ((![14,12,10] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![14,12,10] : Fin 3 → ℤ) i) * fk ((![14,12,10] : Fin 3 → ℤ) i) τ :=
    KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [UpsilonPlusClear, reduceIte, if_neg (show ¬ ((24 : ℕ) = 8) by decide),
    Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_smul_PiMat_entry, PiMatDelta_mul_smul_PiMat_entry, hΔ, hfk]
  rw [zpow_add₀ hτ]
  ring

private lemma UpsilonMinusClear_S_8 (z τ : ℍ) (i j : Fin 3) :
    UpsilonMinusClear 8 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![4,2,0] : Fin 3 → ℤ) i)) * UpsilonMinusClear 8 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
    KernelFacts.jInvariantFun_S_smul τ
  have hΔ : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ (12 : ℤ) * DeltaFun τ :=
    KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ
  have hfk : fk ((![4,2,0] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![4,2,0] : Fin 3 → ℤ) i) * fk ((![4,2,0] : Fin 3 → ℤ) i) τ :=
    KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [UpsilonMinusClear, reduceIte, Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_PiMat_entry, PiMatDelta_mul_PiMat_entry, hΔ, hfk]
  rw [zpow_add₀ hτ]
  ring

private lemma UpsilonMinusClear_S_24 (z τ : ℍ) (i j : Fin 3) :
    UpsilonMinusClear 24 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![12,10,8] : Fin 3 → ℤ) i)) * UpsilonMinusClear 24 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
    KernelFacts.jInvariantFun_S_smul τ
  have hΔ : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ (12 : ℤ) * DeltaFun τ :=
    KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ
  have hfk : fk ((![12,10,8] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![12,10,8] : Fin 3 → ℤ) i) * fk ((![12,10,8] : Fin 3 → ℤ) i) τ :=
    KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [UpsilonMinusClear, reduceIte, if_neg (show ¬ ((24 : ℕ) = 8) by decide),
    Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_smul_PiMat_entry, PiMatDelta_mul_smul_PiMat_entry, hΔ, hfk]
  rw [zpow_add₀ hτ]
  ring

/-! ## The transformation of the cleared kernels under `τ ↦ S•τ`

Assembling the entrywise laws above with the transformation laws
`phiVec (S•τ) i = -τ^{w_i} phiVec τ i` (`Work.Kernels.KernelFacts.phiVec_S_smul`) and
`psiVec (S•τ) i = τ^{2i} psiVec τ i` (`Work.Kernels.KernelFacts.psiVec_S_smul`), and using
`w_i + (12 + v_i) = d/2 + 12` for the two weight vectors of each case, gives

  `KPlusClear d (S•τ) z = -τ^{d/2+12} KPlusClear d τ z`,
  `KMinusClear ℓ d (S•τ) z =  τ^{d/2+12} KMinusClear ℓ d τ z`. -/

private lemma KPlusClear_S_smul_8 (τ z : ℍ) :
    KPlusClear 8 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (16 : ℤ)) * KPlusClear 8 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  simp only [KPlusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, phiVec (ModularGroup.S • τ) i
          * UpsilonPlusClear 8 (ModularGroup.S • τ) z i j * phitVec z j)
        = -((τ : ℂ) ^ (16 : ℤ)) *
            (∑ j : Fin 3, phiVec τ i * UpsilonPlusClear 8 τ z i j * phitVec z j) := by
    intro i
    have hφ := KernelFacts.phiVec_S_smul τ i
    have hpow : (τ : ℂ) ^ ((![-2,0,2] : Fin 3 → ℤ) i) *
        (τ : ℂ) ^ (12 + ((![6,4,2] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (16 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hφ, UpsilonPlusClear_S_8 z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.mul_sum]

private lemma KPlusClear_S_smul_24 (τ z : ℍ) :
    KPlusClear 24 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (24 : ℤ)) * KPlusClear 24 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  simp only [KPlusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, phiVec (ModularGroup.S • τ) i
          * UpsilonPlusClear 24 (ModularGroup.S • τ) z i j * phitVec z j)
        = -((τ : ℂ) ^ (24 : ℤ)) *
            (∑ j : Fin 3, phiVec τ i * UpsilonPlusClear 24 τ z i j * phitVec z j) := by
    intro i
    have hφ := KernelFacts.phiVec_S_smul τ i
    have hpow : (τ : ℂ) ^ ((![-2,0,2] : Fin 3 → ℤ) i) *
        (τ : ℂ) ^ (12 + ((![14,12,10] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (24 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hφ, UpsilonPlusClear_S_24 z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.mul_sum]

private lemma KMinusClear_S_smul_8 (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinusClear ℓ 8 (ModularGroup.S • τ) z = ((τ : ℂ) ^ (16 : ℤ)) * KMinusClear ℓ 8 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  simp only [KMinusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, psiVec ℓ (ModularGroup.S • τ) i
          * UpsilonMinusClear 8 (ModularGroup.S • τ) z i j * psitVec ℓ z j)
        = ((τ : ℂ) ^ (16 : ℤ)) *
            (∑ j : Fin 3, psiVec ℓ τ i * UpsilonMinusClear 8 τ z i j * psitVec ℓ z j) := by
    intro i
    have hψ := KernelFacts.psiVec_S_smul ℓ τ i
    have hpow : (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) *
        (τ : ℂ) ^ (12 + ((![4,2,0] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (16 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hψ, UpsilonMinusClear_S_8 z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.mul_sum]

private lemma KMinusClear_S_smul_24 (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinusClear ℓ 24 (ModularGroup.S • τ) z = ((τ : ℂ) ^ (24 : ℤ)) * KMinusClear ℓ 24 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero' τ
  simp only [KMinusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, psiVec ℓ (ModularGroup.S • τ) i
          * UpsilonMinusClear 24 (ModularGroup.S • τ) z i j * psitVec ℓ z j)
        = ((τ : ℂ) ^ (24 : ℤ)) *
            (∑ j : Fin 3, psiVec ℓ τ i * UpsilonMinusClear 24 τ z i j * psitVec ℓ z j) := by
    intro i
    have hψ := KernelFacts.psiVec_S_smul ℓ τ i
    have hpow : (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) *
        (τ : ℂ) ^ (12 + ((![12,10,8] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (24 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hψ, UpsilonMinusClear_S_24 z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i)]
  rw [Finset.mul_sum]

/-- **Vanishing of the cleared kernels at the `S`-conjugate pairs (the CKMRV residue `φ(S) = 0`).**

For every `z ∈ ℍ` and `d ∈ {8, 24}` the cleared kernels of `Work.Kernels` vanish at the pair
`(S z, z)`, where `S z = -1/z`.  Together with the diagonal case
(`Work.Residues.KPlusClear_diag`, `Work.Residues.KMinusClear_diag`) this is exactly the
statement that the residues of `K_±` at the two `SL(2,ℤ)`-translates of `z` that can meet the
CKMRV contour (namely `z` itself, `γ = I`, and `S z`, `γ = S`) vanish, i.e. `φ_±(I) = φ_±(S)
= 0` (CKMRV Theorem 4.9(3)).

Cleanest route (pointed out by the reviewer): since `j(S z) = j(z)`, the middle matrices of
`UpsilonPlusClear d` and `UpsilonMinusClear ℓ d` at `τ = S z` are literally the same as at
`τ = z`; only the outer factors `phiVec`, `PiMatDelta`, `psiVec` differ, and by the proven
transformation laws (`phiVec_S_smul`, `fk_S_smul`, `psiVec_S_smul`) they differ by the uniform
scalar `-z^{d/2+12}` (resp. `z^{d/2+12}`):
`KPlusClear d (S z) z = -z^{d/2+12} * KPlusClear d z z` and
`KMinusClear ℓ d (S z) z = z^{d/2+12} * KMinusClear ℓ d z z`,
so `KPlusClear_diag` / `KMinusClear_diag` finish. -/
theorem KClear_S_vanishing (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.KPlusClear d (ModularGroup.S • z) z = 0 ∧
      Work.Kernels.KMinusClear ℓ d (ModularGroup.S • z) z = 0 := by
  rcases hd with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [KPlusClear_S_smul_8 z z, Work.Residues.KPlusClear_diag 8 (Or.inl rfl) z, mul_zero]
    · rw [KMinusClear_S_smul_8 ℓ z z, Work.Residues.KMinusClear_diag ℓ 8 (Or.inl rfl) z,
        mul_zero]
  · refine ⟨?_, ?_⟩
    · rw [KPlusClear_S_smul_24 z z, Work.Residues.KPlusClear_diag 24 (Or.inr rfl) z, mul_zero]
    · rw [KMinusClear_S_smul_24 ℓ z z, Work.Residues.KMinusClear_diag ℓ 24 (Or.inr rfl) z,
        mul_zero]

end Work.Asymptotics
