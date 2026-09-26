import Submission.Work.RouteB.PermAction
import Mathlib

open OnPropertyT Submission.FreeGroupAut
open FreeGroup
open scoped BigOperators

set_option autoImplicit false

/-!
# Equivariance of the Nielsen transvections under the permutation action

Conjugation by `permAut σ` (the automorphism `aᵢ ↦ a_{σ i}`) sends the transvections with
indices `(i,j)` to the transvections with indices `(σ i, σ j)`.  This is the equivariance
needed for the edge Laplacians `Δ_e` of the symmetrisation argument.
-/

namespace Submission.RouteB

variable {n : ℕ}

/-- Conjugation by `permAut σ` sends `ρᵢⱼ` to `ρ_{σ i, σ j}`. -/
theorem permAut_conj_rho (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * rho i j hij * (permAut σ)⁻¹
      = rho (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  show (permAut σ) (rho i j hij ((permAut σ)⁻¹ (FreeGroup.of k)))
      = rho (σ i) (σ j) (fun h => hij (σ.injective h)) (FreeGroup.of k)
  have h1 : (permAut σ)⁻¹ (FreeGroup.of k) = FreeGroup.of (σ.symm k) := by
    rw [permAut_inv, permAut_apply]
  rw [h1]
  by_cases hk : k = σ i
  · subst hk
    have h2 : σ.symm (σ i) = i := Equiv.symm_apply_apply σ i
    rw [h2, rho_apply_self]
    rw [show (permAut σ) (a i * a j) = (permAut σ) (a i) * (permAut σ) (a j) from
      (permAut σ).map_mul _ _, permAut_apply, permAut_apply, rho_apply_self]
  · have h2 : σ.symm k ≠ i := fun h => hk (by
      have := congrArg σ h
      rwa [Equiv.apply_symm_apply] at this)
    rw [rho_apply_other hij h2, permAut_apply,
      rho_apply_other (fun h => hij (σ.injective h)) hk]
    exact congrArg _ (Equiv.apply_symm_apply σ k)

/-- Conjugation by `permAut σ` sends `ρᵢⱼ⁻¹` to `ρ_{σ i, σ j}⁻¹`. -/
theorem permAut_conj_rhoNeg (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * rhoNeg i j hij * (permAut σ)⁻¹
      = rhoNeg (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  rw [← rho_inv_eq i j hij, ← rho_inv_eq (σ i) (σ j) (fun h => hij (σ.injective h))]
  have h : permAut σ * (rho i j hij)⁻¹ * (permAut σ)⁻¹
      = (permAut σ * rho i j hij * (permAut σ)⁻¹)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [h, permAut_conj_rho]

/-- Conjugation by `permAut σ` sends `λᵢⱼ` to `λ_{σ i, σ j}`. -/
theorem permAut_conj_lam (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * lam i j hij * (permAut σ)⁻¹
      = lam (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  show (permAut σ) (lam i j hij ((permAut σ)⁻¹ (FreeGroup.of k)))
      = lam (σ i) (σ j) (fun h => hij (σ.injective h)) (FreeGroup.of k)
  have h1 : (permAut σ)⁻¹ (FreeGroup.of k) = FreeGroup.of (σ.symm k) := by
    rw [permAut_inv, permAut_apply]
  rw [h1]
  by_cases hk : k = σ i
  · subst hk
    have h2 : σ.symm (σ i) = i := Equiv.symm_apply_apply σ i
    rw [h2, lam_apply_self]
    rw [show (permAut σ) (a j * a i) = (permAut σ) (a j) * (permAut σ) (a i) from
      (permAut σ).map_mul _ _, permAut_apply, permAut_apply, lam_apply_self]
  · have h2 : σ.symm k ≠ i := fun h => hk (by
      have := congrArg σ h
      rwa [Equiv.apply_symm_apply] at this)
    rw [lam_apply_other hij h2, permAut_apply,
      lam_apply_other (fun h => hij (σ.injective h)) hk]
    exact congrArg _ (Equiv.apply_symm_apply σ k)

/-- Conjugation by `permAut σ` sends `λᵢⱼ⁻¹` to `λ_{σ i, σ j}⁻¹`. -/
theorem permAut_conj_lamNeg (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * lamNeg i j hij * (permAut σ)⁻¹
      = lamNeg (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  rw [← lam_inv_eq i j hij, ← lam_inv_eq (σ i) (σ j) (fun h => hij (σ.injective h))]
  have h : permAut σ * (lam i j hij)⁻¹ * (permAut σ)⁻¹
      = (permAut σ * lam i j hij * (permAut σ)⁻¹)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [h, permAut_conj_lam]

end Submission.RouteB
