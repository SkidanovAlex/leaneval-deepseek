/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `B ⊗_A B ≅ ∏_σ B` for `B = A ⊗_k k'` and `k'/k` finite Galois

The Galois isomorphism `k' ⊗_k k' ≅ ∏_{σ ∈ Gal(k'/k)} k'`, `x ⊗ y ↦ (σ ↦ σ x * y)`, base changed
along `k → A`:

  `(A ⊗_k k') ⊗_A (A ⊗_k k') ≅ ∏_{σ ∈ Gal(k'/k)} (A ⊗_k k')`, `x ⊗_A y ↦ (σ ↦ σ x * y)`,

where `σ` acts on the second tensor factor of `A ⊗_k k'`.  Equivalently, the `A`-algebra map
`Algebra.TensorProduct.lift (galoisLeftA k k' A) (galoisRightA k k' A) _` is bijective.

The proof is by base change of the `k`-version (`galoisSelfTensorOverK_bijective`): the source is
identified with `A ⊗_k (k' ⊗_k k')` by `TensorProduct.AlgebraTensorModule.distribBaseChange`, and
the target with `A ⊗_k (∏_σ k')` by `TensorProduct.piRight`; both are isomorphisms, so the map is
the base change `id_A ⊗ (k' ⊗_k k' ≅ ∏_σ k')` of an isomorphism.
-/
import Mathlib
import Submission.Work.Descent.QuotientSetup
import Submission.Work.Descent.GaloisBasis
import Submission.Work.Descent.exists_coeffs_left

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

namespace Work.Descent

universe u

section KVersion

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [IsGalois k k']

/-- The `k`-algebra map `k' ⊗_k k' → ∏_{σ ∈ Gal(k'/k)} k'`, `x ⊗ y ↦ (σ ↦ σ x * y)`. -/
noncomputable def galoisSelfTensorOverKLift : (k' ⊗[k] k') →ₐ[k] (Gal k k' → k') :=
  Algebra.TensorProduct.lift (galoisLeft k k') (galoisRight k k') (fun _ _ => Commute.all _ _)

omit [FiniteDimensional k k'] [IsGalois k k'] in
@[simp] lemma galoisSelfTensorOverKLift_tmul (x y : k') :
    galoisSelfTensorOverKLift (k := k) (k' := k') (x ⊗ₜ[k] y) = fun σ : Gal k k' => σ x * y := by
  rw [galoisSelfTensorOverKLift, Algebra.TensorProduct.lift_tmul]
  ext σ
  simp [galoisLeft, galoisRight]

/-- The map `galoisSelfTensorOverKLift` is surjective: the dual coefficients provided by
`Work.Descent.exists_coeffs_left` for the Galois matrix `(σ (c τ))` exhibit the "basis" vectors
`Pi.single σ c` of the product in its image. -/
lemma galoisSelfTensorOverK_surjective :
    Function.Surjective (galoisSelfTensorOverKLift (k := k) (k' := k')) := by
  classical
  intro w
  have hsingle : ∀ (σ₀ : Gal k k') (c : k'), ∃ z : k' ⊗[k] k',
      galoisSelfTensorOverKLift (k := k) (k' := k') z = Pi.single σ₀ c := by
    intro σ₀ c
    obtain ⟨l, hl1, hl2⟩ := exists_coeffs_left (galoisBasis k k') σ₀
    refine ⟨∑ τ, (galoisBasis k k' τ) ⊗ₜ[k] (c * l τ), ?_⟩
    rw [map_sum]
    ext σ
    rw [Finset.sum_apply]
    simp only [galoisSelfTensorOverKLift_tmul]
    have hsum : (∑ τ : Gal k k', σ (galoisBasis k k' τ) * (c * l τ))
        = c * (∑ τ : Gal k k', l τ * σ (galoisBasis k k' τ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun τ _ => by ring)
    rw [hsum]
    rcases eq_or_ne σ σ₀ with h | h
    · subst h; rw [hl1, mul_one, Pi.single_eq_same]
    · rw [hl2 σ h, mul_zero, Pi.single_eq_of_ne h]
  have hw : w = ∑ σ : Gal k k', Pi.single σ (w σ) := by
    ext σ; simp
  rw [hw]
  choose z hz using hsingle
  exact ⟨∑ σ : Gal k k', z σ (w σ), by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun σ _ => hz σ (w σ))⟩

/-- `galoisSelfTensorOverKLift` is bijective.  Since it is injective iff surjective for linear maps
between finite-dimensional spaces of the same dimension, it suffices to compare `finrank`s, which are
both `[k' : k] ^ 2`. -/
lemma galoisSelfTensorOverK_bijective :
    Function.Bijective (galoisSelfTensorOverKLift (k := k) (k' := k')) := by
  have hsurj := galoisSelfTensorOverK_surjective (k := k) (k' := k')
  have hfin : Module.finrank k (k' ⊗[k] k') = Module.finrank k (Gal k k' → k') := by
    rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← IsGalois.card_aut_eq_finrank k k', smul_eq_mul]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (galoisSelfTensorOverKLift (k := k) (k' := k')).toLinearMap) hfin).mpr hsurj, hsurj⟩

/-- The `k`-algebra isomorphism `k' ⊗_k k' ≅ ∏_{σ ∈ Gal(k'/k)} k'`, `x ⊗ y ↦ (σ ↦ σ x * y)`. -/
noncomputable def galoisSelfTensorOverKAlgEquiv : (k' ⊗[k] k') ≃ₐ[k] (Gal k k' → k') :=
  AlgEquiv.ofBijective (galoisSelfTensorOverKLift (k := k) (k' := k'))
    (galoisSelfTensorOverK_bijective (k := k) (k' := k'))

@[simp] lemma galoisSelfTensorOverKAlgEquiv_tmul (x y : k') :
    galoisSelfTensorOverKAlgEquiv (k := k) (k' := k') (x ⊗ₜ[k] y) = fun σ : Gal k k' => σ x * y := by
  rw [galoisSelfTensorOverKAlgEquiv, AlgEquiv.ofBijective_apply, galoisSelfTensorOverKLift_tmul]

/-- The same isomorphism, as a linear equivalence. -/
noncomputable def galoisSelfTensorOverKEquiv : (k' ⊗[k] k') ≃ₗ[k] (Gal k k' → k') :=
  (galoisSelfTensorOverKAlgEquiv (k := k) (k' := k')).toLinearEquiv

@[simp] lemma galoisSelfTensorOverKEquiv_tmul (x y : k') :
    galoisSelfTensorOverKEquiv (k := k) (k' := k') (x ⊗ₜ[k] y) = fun σ : Gal k k' => σ x * y := by
  rw [galoisSelfTensorOverKEquiv, AlgEquiv.coe_toLinearEquiv, galoisSelfTensorOverKAlgEquiv_tmul]

end KVersion

/-- Base change to an arbitrary `k`-algebra `A` of the Galois isomorphism `k' ⊗_k k' ≅ ∏_σ k'`:
the `A`-algebra map `(A ⊗_k k') ⊗_A (A ⊗_k k') → ∏_σ (A ⊗_k k')`, `x ⊗_A y ↦ (σ ↦ σ x * y)`, is
bijective. -/
theorem galoisTensorSelfOver_bijective {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective (Algebra.TensorProduct.lift (Work.Descent.galoisLeftA k k' A)
      (Work.Descent.galoisRightA k k' A) (fun _ _ => Commute.all _ _)) := by
  classical
  -- the `k`-version, as a linear equivalence
  let ek : (k' ⊗[k] k') ≃ₗ[k] (Gal k k' → k') := galoisSelfTensorOverKEquiv (k := k) (k' := k')
  have ek_tmul : ∀ (x y : k'), ek (x ⊗ₜ[k] y) = (fun σ : Gal k k' => σ x * y) :=
    fun x y => galoisSelfTensorOverKEquiv_tmul (k := k) (k' := k') x y
  -- source identification `(A ⊗_k k') ⊗_A (A ⊗_k k') ≅ A ⊗_k (k' ⊗_k k')`
  let D : (A ⊗[k] k') ⊗[A] (A ⊗[k] k') ≃ₗ[A] A ⊗[k] (k' ⊗[k] k') :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange k A k' k').symm
  have D_tmul : ∀ (a b : A) (x y : k'),
      D ((a ⊗ₜ[k] x) ⊗ₜ[A] (b ⊗ₜ[k] y)) = ((a * b) ⊗ₜ[k] (x ⊗ₜ[k] y)) :=
    fun a b x y => TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul k A x y a b
  -- base change of `ek` to `A`
  let W : A ⊗[k] (k' ⊗[k] k') ≃ₗ[A] A ⊗[k] (Gal k k' → k') :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) ek
  have W_tmul : ∀ (a : A) (z : k' ⊗[k] k'), W (a ⊗ₜ[k] z) = a ⊗ₜ[k] ek z :=
    fun a z => TensorProduct.AlgebraTensorModule.congr_tmul (LinearEquiv.refl A A) ek a z
  -- target identification `A ⊗_k (∏_σ k') ≅ ∏_σ (A ⊗_k k')`
  let C : A ⊗[k] (Gal k k' → k') ≃ₗ[A] (Gal k k' → A ⊗[k] k') :=
    TensorProduct.piRight k A A (fun _ : Gal k k' => k')
  have C_tmul : ∀ (a : A) (f : Gal k k' → k'), C (a ⊗ₜ[k] f) = (fun σ => a ⊗ₜ[k] f σ) := fun a f => by
    change TensorProduct.piRightHom k A A (fun _ : Gal k k' => k') (a ⊗ₜ[k] f)
      = (fun σ => a ⊗ₜ[k] f σ)
    rw [TensorProduct.piRightHom_tmul]
  -- the two maps agree on pure tensors, hence everywhere
  have heq : ⇑(Algebra.TensorProduct.lift (galoisLeftA k k' A) (galoisRightA k k' A)
        (fun _ _ => Commute.all _ _)) = ⇑(D.trans (W.trans C)) := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      induction x using TensorProduct.inductionOn with
      | tmul a u =>
        induction y using TensorProduct.inductionOn with
        | tmul b v =>
          rw [Algebra.TensorProduct.lift_tmul, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
            D_tmul, W_tmul, C_tmul, ek_tmul]
          ext σ
          simp [galoisLeftA, galoisRightA, baseChangeAlgEquiv_tmul,
            Algebra.TensorProduct.tmul_mul_tmul]
        | add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | add x1 x2 h1 h2 => rw [TensorProduct.add_tmul, map_add, map_add, h1, h2]
    | add z1 z2 h1 h2 => rw [map_add, map_add, h1, h2]
  rw [show ⇑(Algebra.TensorProduct.lift (galoisLeftA k k' A) (galoisRightA k k' A)
        (fun _ _ => Commute.all _ _)) = ⇑(D.trans (W.trans C)) from heq]
  exact (D.trans (W.trans C)).bijective

end Work.Descent
