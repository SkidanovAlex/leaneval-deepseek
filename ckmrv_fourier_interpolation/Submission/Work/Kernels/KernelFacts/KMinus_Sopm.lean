/-
# `S - I` annihilation of the kernel `K_-^{(d)}` (CKMRV Theorem 4.9)

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) build the kernel

  `K_-^{(d)}(τ,z) = ψ⃗(τ)ᵗ · Υ_-^{(d)}(τ,z) · ψ̃⃗(z)`

for `d = 8, 24`, and `K_-^{(d)}` is, as a function of `τ`, annihilated by the right ideal
`𝓘₊ = (S+I)R + (T-I)²R` of `R = ℂ[SL(2,ℤ)]` at weight `d/2`.  This file proves the `S - I`
half of that statement in the form recorded by `Work.Kernels.Sopm`:

  `Sopm (d/2) (fun τ ↦ K_-^{(d)}(τ,z)) = 0`,  i.e.  `(K_-^{(d)}(·,z) ∣[d/2] S) = K_-^{(d)}(·,z)`.

The two ingredients mirror the corresponding statement for `K_+^{(d)}`
(`Work.Kernels.KernelFacts.KPlus_S_add`):

* the basis `(ψ_0, ψ_2, ψ_4) = (1, ψ_2, ψ_4)` of Proposition 4.3 satisfies
  `Sopm (2i) (ψ_i) = 0` for `i = 0, 1, 2`, i.e. `ψ_i(S•τ) = τ^{2i} ψ_i(τ)`
  (`Sopm_one`, `psi2_Sopm`, `psi4_Sopm`);
* the `τ`-dependence of the coefficient matrix `Υ_-^{(d)}` is only through the diagonal
  factor `Π_{d/2, d/2-2, d/2-4}(τ)` (with `f_k` modular of weight `k`) and the
  `S`-invariant expressions `j(τ)` and `j(τ) - j(z)`, so that entrywise
  `Υ_-^{(d)}(S•τ,z)_{ij} = τ^{d/2 - 2i} Υ_-^{(d)}(τ,z)_{ij}`.

Since `2i + (d/2 - 2i) = d/2`, the `τ`-powers of the two factors combine to `τ^{d/2}` and
`K_-^{(d)}(S•τ,z) = τ^{d/2} K_-^{(d)}(τ,z)`, which is exactly `Sopm (d/2) = 0`.

## Main result

* `Work.Kernels.KernelFacts.KMinus_Sopm`.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.psi2_Sopm
import Submission.Work.Kernels.KernelFacts.psi4_Sopm
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

open Work.Kernels

/-! ## Pointwise transformation laws under `τ ↦ S • τ` -/

/-- A function killed by `S - I` at weight `k` satisfies the pointwise law
`F(S•τ) = τ^k F(τ)`. -/
lemma smul_of_sopm {k : ℤ} {F : ℍ → ℂ} (h : Sopm k F = 0) (τ : ℍ) :
    F (ModularGroup.S • τ) = (τ : ℂ) ^ k * F τ := by
  have hF : F ∣[k] ModularGroup.S = F := by
    ext σ
    have hσ := congr_fun h σ
    simp only [Sopm, Pi.zero_apply] at hσ
    exact sub_eq_zero.mp hσ
  have h1 : F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) = F τ := by
    rw [← slash_S_apply k F τ, hF]
  have hτ : (τ : ℂ) ≠ 0 := kpc_tau_ne_zero τ
  calc F (ModularGroup.S • τ) = F (ModularGroup.S • τ) * 1 := by rw [mul_one]
    _ = F (ModularGroup.S • τ) * ((τ : ℂ) ^ (-k) * (τ : ℂ) ^ k) := by
          rw [← zpow_add₀ hτ, neg_add_cancel, zpow_zero]
    _ = (F (ModularGroup.S • τ) * (τ : ℂ) ^ (-k)) * (τ : ℂ) ^ k := by rw [mul_assoc]
    _ = F τ * (τ : ℂ) ^ k := by rw [h1]
    _ = (τ : ℂ) ^ k * F τ := by rw [mul_comm]

/-- The basis `(ψ_0, ψ_2, ψ_4) = (1, ψ_2, ψ_4)` of Proposition 4.3 transforms by
`ψ_i(S•τ) = τ^{2i} ψ_i(τ)`. -/
lemma psiVec_S_smul (ℓ : LogLambdaData) (τ : ℍ) (i : Fin 3) :
    psiVec ℓ (ModularGroup.S • τ) i = (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) * psiVec ℓ τ i := by
  fin_cases i
  · show psiVec ℓ (ModularGroup.S • τ) 0 =
        (τ : ℂ) ^ (2 * (((0 : Fin 3) : ℕ) : ℤ)) * psiVec ℓ τ 0
    simp [psiVec]
  · show psiVec ℓ (ModularGroup.S • τ) 1 =
        (τ : ℂ) ^ (2 * (((1 : Fin 3) : ℕ) : ℤ)) * psiVec ℓ τ 1
    rw [show (2 * (((1 : Fin 3) : ℕ) : ℤ)) = (2 : ℤ) by norm_num]
    simp only [psiVec, Matrix.cons_val_one]
    exact smul_of_sopm (psi2_Sopm ℓ) τ
  · show psiVec ℓ (ModularGroup.S • τ) 2 =
        (τ : ℂ) ^ (2 * (((2 : Fin 3) : ℕ) : ℤ)) * psiVec ℓ τ 2
    rw [show (2 * (((2 : Fin 3) : ℕ) : ℤ)) = (4 : ℤ) by norm_num]
    simp only [psiVec, Matrix.cons_val_two]
    exact smul_of_sopm (psi4_Sopm ℓ) τ

/-- Entrywise transformation of the coefficient matrix `Υ_-^{(d)}` under `τ ↦ S • τ`. -/
lemma UpsilonMinus_S (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonMinus d (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ ((d : ℤ) / 2 - 2 * ((i : ℕ) : ℤ)) * UpsilonMinus d τ z i j := by
  have hJ : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ := kpc_jInvariant_S τ
  rcases hd with rfl | rfl
  · have hPi := kpc_PiMat_S (![4, 2, 0] : Fin 3 → ℤ) τ
    simp only [UpsilonMinus, reduceIte]
    rw [hJ, hPi]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    rw [Matrix.diagonal_mul]
    have hai : (((![4, 2, 0] : Fin 3 → ℤ) i : ℤ)) =
        ((8 : ℕ) : ℤ) / 2 - 2 * ((i : ℕ) : ℤ) := by
      fin_cases i <;> norm_num
    rw [← hai]
    ring
  · have hPi := kpc_PiMat_S (![12, 10, 8] : Fin 3 → ℤ) τ
    simp only [UpsilonMinus, reduceIte]
    simp only [if_neg (show ¬((24 : ℕ) = 8) by decide)]
    rw [hJ, hPi]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
    rw [Matrix.diagonal_mul]
    have hai : (((![12, 10, 8] : Fin 3 → ℤ) i : ℤ)) =
        ((24 : ℕ) : ℤ) / 2 - 2 * ((i : ℕ) : ℤ) := by
      fin_cases i <;> norm_num
    rw [← hai]
    ring

/-- `K_-^{(d)}(S•τ,z) = τ^{d/2} K_-^{(d)}(τ,z)` for `d = 8` and `d = 24`. -/
lemma KMinus_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z τ : ℍ) :
    KMinus ℓ d (ModularGroup.S • τ) z = (τ : ℂ) ^ ((d : ℤ) / 2) * KMinus ℓ d τ z := by
  have hτ : (τ : ℂ) ≠ 0 := kpc_tau_ne_zero τ
  simp only [KMinus]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpow : (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) *
      (τ : ℂ) ^ ((d : ℤ) / 2 - 2 * ((i : ℕ) : ℤ)) = (τ : ℂ) ^ ((d : ℤ) / 2) := by
    rw [← zpow_add₀ hτ]; congr 1; ring
  rw [psiVec_S_smul ℓ τ i, UpsilonMinus_S d hd z i j τ, ← hpow]
  ring

/-! ## The main theorem -/

theorem KMinus_Sopm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.Sopm ((d : ℤ) / 2) (fun τ : UpperHalfPlane => Work.Kernels.KMinus ℓ d τ z) = 0 := by
  ext τ
  simp only [Sopm, Pi.zero_apply]
  rw [slash_S_apply, KMinus_S_smul ℓ d hd z τ]
  have hτ : (τ : ℂ) ≠ 0 := kpc_tau_ne_zero τ
  have h1 : (τ : ℂ) ^ ((d : ℤ) / 2) * (τ : ℂ) ^ (-((d : ℤ) / 2)) = 1 := by
    rw [← zpow_add₀ hτ, add_neg_cancel, zpow_zero]
  rw [show ((τ : ℂ) ^ ((d : ℤ) / 2) * KMinus ℓ d τ z) * (τ : ℂ) ^ (-((d : ℤ) / 2)) =
      ((τ : ℂ) ^ ((d : ℤ) / 2) * (τ : ℂ) ^ (-((d : ℤ) / 2))) * KMinus ℓ d τ z by ring,
    h1, one_mul, sub_self]

end Work.Kernels.KernelFacts
