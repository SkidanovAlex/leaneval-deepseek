/-
# Vanishing of a group hom into a `k`-module when `N_ab ⊗_ℤ k = 0`

This file proves `Work.ORFP2.eq_one_of_subsingleton_abelianizationTensor`, needed for the
`FP₂`/Bieri–Strebel part of the route.

The mathematical content is the tensor–hom adjunction.  If `A` is a `k`-module and `M` is a
`ℤ`-module with `M ⊗[ℤ] k = 0`, then every `ℤ`-linear map `M →ₗ[ℤ] A` is zero: the extension
of scalars of such a map along `ℤ → k` is a `k`-linear map `M ⊗[ℤ] k →ₗ[ℤ] A` out of the zero
module, and evaluating it on `x ⊗ₜ 1` recovers `ψ x`.

Applying this to `M = Additive (Abelianization N)` and to the `ℤ`-linear map induced by a
monoid homomorphism `β : N →* Multiplicative A` (which factors through the abelianization
because `Multiplicative A` is commutative) gives `β n = 1` for every `n : N`.
-/
import Mathlib

open scoped TensorProduct

namespace Work.ORFP2

/-- **A `ℤ`-linear map into a `k`-module out of a module with `M ⊗[ℤ] k = 0` is zero.**

This is the (easy) direction of the tensor–hom adjunction
`Hom_ℤ(M, A) ≅ Hom_k(M ⊗[ℤ] k, A)` for a `k`-module `A`. -/
lemma intLinearMap_eq_zero_of_subsingleton_tensor {k : Type*} [CommRing k] {M : Type*}
    [AddCommGroup M] {A : Type*} [AddCommGroup A] [Module k A] (ψ : M →ₗ[ℤ] A)
    (h : Subsingleton (M ⊗[ℤ] k)) : ∀ x : M, ψ x = 0 := by
  intro x
  -- The `ℤ`-bilinear map `M × k → A`, `(m, c) ↦ c • ψ m`, as a curried `ℤ`-linear map.
  let f : M →ₗ[ℤ] (k →ₗ[ℤ] A) :=
    { toFun := fun m =>
        { toFun := fun c => c • ψ m
          map_add' := fun c c' => by rw [add_smul]
          map_smul' := fun z c => smul_assoc z c (ψ m) }
      map_add' := fun m m' => by
        ext c
        change c • ψ (m + m') = c • ψ m + c • ψ m'
        rw [ψ.map_add, smul_add]
      map_smul' := fun z m => by
        ext c
        change c • ψ (z • m) = z • (c • ψ m)
        rw [ψ.map_smul]
        exact (smul_comm z c (ψ m)).symm }
  -- Evaluation at `x ⊗ₜ 1` recovers `ψ x`.
  have hkey : (TensorProduct.lift f) (x ⊗ₜ[ℤ] (1 : k)) = ψ x := by
    rw [TensorProduct.lift.tmul]
    show (1 : k) • ψ x = ψ x
    rw [one_smul]
  calc ψ x = (TensorProduct.lift f) (x ⊗ₜ[ℤ] (1 : k)) := hkey.symm
    _ = (TensorProduct.lift f) 0 := by rw [h.elim (x ⊗ₜ[ℤ] (1 : k)) 0]
    _ = 0 := map_zero _

/-- If `N_ab ⊗_ℤ k = 0` and `A` is a `k`-module, then any monoid homomorphism
`β : N →* Multiplicative A` is trivial. -/
theorem eq_one_of_subsingleton_abelianizationTensor (k : Type*) [CommRing k] {N : Type*} [Group N]
    {A : Type*} [AddCommGroup A] [Module k A] (β : N →* Multiplicative A)
    (h : Subsingleton (TensorProduct ℤ (Additive (Abelianization N)) k)) :
    ∀ n : N, β n = 1 := by
  intro n
  -- `β` lands in a commutative group, so it factors through the abelianization of `N`.
  let γ : Abelianization N →* Multiplicative A := Abelianization.lift β
  have hγ : γ (Abelianization.of n) = β n := Abelianization.lift_apply_of β n
  -- `γ` is an additive homomorphism `Additive (Abelianization N) → A`, hence `ℤ`-linear.
  let ψ : Additive (Abelianization N) →ₗ[ℤ] A :=
    AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive γ)
  have hψ : ψ (Additive.ofMul (Abelianization.of n)) = 0 :=
    intLinearMap_eq_zero_of_subsingleton_tensor ψ h _
  have h1 : ψ (Additive.ofMul (Abelianization.of n)) = β n := rfl
  rw [h1] at hψ
  exact hψ

end Work.ORFP2
