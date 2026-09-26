/-
# Linearity of the group-algebra action, and the functional equations of the kernels

This file records the two linearity properties of the group-algebra action `slash` with
respect to the *function* variable, which are what allow the functional equations of the
kernels `K_±` to be reduced to finitely many scalar identities for the basis functions
`φ_{-2}, φ_0, φ_2` and `ψ_0, ψ_2, ψ_4` (CKMRV Propositions 4.2 and 4.3).

## Main results

* `Work.Kernels.slash_add_F`: `slash` is additive in the function variable.
* `Work.Kernels.slash_smul_F`: `slash` is `ℂ`-homogeneous in the function variable.
* `Work.Kernels.KPlus_eq_sum`: `K_+^{(d)}(τ,z) = ∑_i φ_i(τ) · c_i(τ)` with
  `c_i(τ) = ∑_j Υ_+^{(d)}(τ,z)_{ij} φ̃_j(z)`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

lemma slash_add_F (k : ℤ) (r : R) (F G : ℍ → ℂ) :
    slash k r (F + G) = slash k r F + slash k r G := by
  simp only [slash, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  rw [SlashAction.add_slash, smul_add]

lemma slash_smul_F (k : ℤ) (r : R) (c : ℂ) (F : ℍ → ℂ) :
    slash k r (c • F) = c • slash k r F := by
  simp only [slash]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro γ hγ
  ext τ
  simp only [Pi.smul_apply, smul_eq_mul, SL_smul_slash]
  ring

/-- The `i`-th coefficient function of `K_+^{(d)}(·,z)`, namely
`c_i(τ) = ∑_j Υ_+^{(d)}(τ,z)_{ij} φ̃_j(z)`. -/
def KPlusCoeff (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) : ℂ :=
  ∑ j : Fin 3, UpsilonPlus d τ z i j * phitVec z j

/-- The `i`-th coefficient function of `K_-^{(d)}(·,z)`. -/
def KMinusCoeff (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) (i : Fin 3) (τ : ℍ) : ℂ :=
  ∑ j : Fin 3, UpsilonMinus d τ z i j * psitVec ℓ z j

lemma KPlus_eq_sum (d : ℕ) (τ z : ℍ) :
    KPlus d τ z = ∑ i : Fin 3, phiVec τ i * KPlusCoeff d z i τ := by
  simp only [KPlus, KPlusCoeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma KMinus_eq_sum (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    KMinus ℓ d τ z = ∑ i : Fin 3, psiVec ℓ τ i * KMinusCoeff ℓ d z i τ := by
  simp only [KMinus, KMinusCoeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Work.Kernels
