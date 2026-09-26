/-
# `S`-invariance of `ψ_2 = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022), Proposition 4.3)
introduce the function

  `ψ_2 = ξ₂·𝓛 + (ξ₂|₂S)·𝓛_S`

and show that it lies in the space `Ann₂(𝓘₊, 𝒫)`, i.e. that it is annihilated by the right
ideal `𝓘₊ = (S+I)R + (T-I)²R` at weight `2`.  This file proves the `S`-part,

  `Sopm 2 (ψ_2) = 0`,  i.e.  `ψ_2 ∣[2] S = ψ_2`,

the `S - I` half of the statement.

The proof is representation-theoretic and makes no use of the explicit shape of `ξ₂`:

* the slash action is a right action (`SlashAction.slash_mul`), so
  `(F ∣[2] S) ∣[2] S = F ∣[2] (S·S)`;
* `S·S = -1` in `SL(2,ℤ)`, and `-1` acts trivially on functions at even weight
  (`(-1 : SL(2,ℤ)) • τ = τ` and `j(-1,τ) = -1`, so the factor of automorphy is `(-1)^{-2} = 1`),
  hence `(ξ₂ ∣[2] S) ∣[2] S = ξ₂`;
* the product rule `ModularForm.mul_slash_SL2` distributes the slash over the two products
  `ξ₂·𝓛` and `(ξ₂|₂S)·𝓛_S`, and the transformation laws of the data `ℓ : LogLambdaData`
  (`ℓ.slash_S : 𝓛 ∣[0] S = 𝓛_S`, `ℓ.slash_S_S : 𝓛_S ∣[0] S = 𝓛`) swap the two terms.

The result is therefore `(ψ_2 ∣[2] S) = (ξ₂|₂S)·𝓛_S + ξ₂·𝓛 = ψ_2`.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelFacts

open Work.Kernels

/-! ## The element `-1 ∈ SL(2,ℤ)` and its slash action at even weight -/

/-- The matrix entries of `-1 ∈ SL(2,ℤ)`. -/
private lemma SL_neg_one_entry_zero_zero :
    (↑(-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 := by decide

private lemma SL_neg_one_entry_zero_one :
    (↑(-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by decide

private lemma SL_neg_one_entry_one_zero :
    (↑(-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by decide

private lemma SL_neg_one_entry_one_one :
    (↑(-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by decide

/-- `-1 ∈ SL(2,ℤ)` acts trivially on `ℍ`. -/
private lemma SL_neg_one_smul (τ : ℍ) : ((-1 : SL(2, ℤ)) • τ) = τ := by
  apply UpperHalfPlane.coe_injective
  rw [Work.Kernels.coe_smul_eq, Work.Kernels.nFun_apply, Work.Kernels.jFun_apply]
  rw [SL_neg_one_entry_zero_zero, SL_neg_one_entry_zero_one,
    SL_neg_one_entry_one_zero, SL_neg_one_entry_one_one]
  push_cast
  field_simp
  ring

/-- The factor of automorphy of `-1 ∈ SL(2,ℤ)` is the constant `-1`. -/
private lemma jFun_neg_one (z : ℂ) : Work.Kernels.jFun (-1 : SL(2, ℤ)) z = -1 := by
  rw [Work.Kernels.jFun_apply, SL_neg_one_entry_one_zero, SL_neg_one_entry_one_one]
  push_cast
  ring

/-- At weight `2`, the slash action of `-1 ∈ SL(2,ℤ)` is trivial. -/
private lemma slash_neg_one_two (f : ℍ → ℂ) : f ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = f := by
  ext τ
  rw [Work.Kernels.slash_apply', SL_neg_one_smul, jFun_neg_one]
  norm_num

/-- The slash action of `S` at weight `2` is an involution: `S² = -1` and `-1` acts trivially
at even weight. -/
private lemma slash_S_S_two (f : ℍ → ℂ) :
    (f ∣[(2 : ℤ)] ModularGroup.S) ∣[(2 : ℤ)] ModularGroup.S = f := by
  have h := SlashAction.slash_mul (2 : ℤ) ModularGroup.S ModularGroup.S f
  rw [show (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 from by decide] at h
  rw [slash_neg_one_two] at h
  exact h.symm

/-- The slash product rule for `S` with a weight-`0` second factor. -/
private lemma mul_slash_S_zero (k : ℤ) (f g : ℍ → ℂ) :
    (f * g) ∣[k] ModularGroup.S
      = (f ∣[k] ModularGroup.S) * (g ∣[(0 : ℤ)] ModularGroup.S) := by
  have h := ModularForm.mul_slash_SL2 k 0 ModularGroup.S f g
  rw [add_zero] at h
  exact h

/-! ## The main statement -/

theorem psi2_Sopm (ℓ : Work.Kernels.LogLambdaData) : Work.Kernels.Sopm 2 (Work.Kernels.psi2 ℓ) = 0 := by
  -- `ψ_2` is the sum of the two products `ξ₂·𝓛` and `(ξ₂|₂S)·𝓛_S`.
  have hpsi : Work.Kernels.psi2 ℓ
      = Work.Kernels.xi2Fun * ℓ.L
        + (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) * ℓ.L_S := by
    funext τ; rfl
  have hmain : Work.Kernels.psi2 ℓ ∣[(2 : ℤ)] ModularGroup.S = Work.Kernels.psi2 ℓ := by
    rw [hpsi, SlashAction.add_slash]
    -- distribute the slash over the two products
    rw [mul_slash_S_zero (2 : ℤ) Work.Kernels.xi2Fun ℓ.L]
    rw [mul_slash_S_zero (2 : ℤ)
      (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) ℓ.L_S]
    -- the transformation laws of `𝓛`, `𝓛_S` and the involution `(ξ₂|₂S)|₂S = ξ₂` swap the terms
    rw [ℓ.slash_S, ℓ.slash_S_S, slash_S_S_two]
    exact add_comm _ _
  change Work.Kernels.psi2 ℓ ∣[(2 : ℤ)] ModularGroup.S - Work.Kernels.psi2 ℓ = 0
  rw [hmain, sub_self]

end Work.Kernels.KernelFacts
