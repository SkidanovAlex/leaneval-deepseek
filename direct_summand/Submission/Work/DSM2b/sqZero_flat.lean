import Mathlib

/-!
# Square-zero descent for flatness

If `I ⊆ A` is an ideal with `I ^ 2 = ⊥`, `M` is an `A`-module such that `M ⧸ I • ⊤` is flat over
`A ⧸ I` and the multiplication map `I ⊗[A] M → M` is injective, then `M` is flat over `A`.

The proof compares, for a finitely generated ideal `J ⊆ A`, the two short exact sequences
`J ⊓ I → J → J ⧸ J ⊓ I → 0` and `I • ⊤ → M → M ⧸ I • ⊤ → 0`: after tensoring with `M` the outer
maps are injective (the first because `J ⧸ J ⊓ I` and `M ⧸ I • ⊤` are modules over `A ⧸ I` with
the latter flat, the second because `M ⧸ I • ⊤` is flat over `A ⧸ I` and `I ⊗[A] M → M` is
injective), and a diagram chase upgrades this to injectivity of `J ⊗[A] M → M`.
-/

namespace Work.DSM2b

universe u

open TensorProduct

section Ident

variable {A : Type u} [CommRing A]

/-- **Change of rings for tensors.**  For an `A ⧸ I`-module `N`, tensoring with `M` over `A` is
the same as tensoring with `M ⧸ I • ⊤` over `A ⧸ I`. -/
noncomputable def tensorQuotEquiv (I : Ideal A) (N M : Type u) [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] [AddCommGroup M] [Module A M] :
    N ⊗[A] M ≃ₗ[A ⧸ I] N ⊗[A ⧸ I] (M ⧸ I • (⊤ : Submodule A M)) :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) N M).symm).trans
    (LinearEquiv.lTensor N (LinearEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
      (TensorProduct.quotTensorEquivQuotSMul M I)))

end Ident


section IdentSimp

variable {A : Type u} [CommRing A] (I : Ideal A)

@[simp]
lemma tensorQuotEquiv_tmul {N M : Type u} [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] [AddCommGroup M] [Module A M]
    (n : N) (m : M) :
    tensorQuotEquiv I N M (n ⊗ₜ[A] m) = n ⊗ₜ[A ⧸ I] (Submodule.Quotient.mk m) := by
  rw [tensorQuotEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  simp

end IdentSimp

section Naturality

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {N N' M : Type u}
  [AddCommGroup N] [Module A N] [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N]
  [AddCommGroup N'] [Module A N'] [Module (A ⧸ I) N'] [IsScalarTower A (A ⧸ I) N']
  [AddCommGroup M] [Module A M]

/-- **Naturality of `tensorQuotEquiv` in the first variable.**  For an `A ⧸ I`-linear map `f`,
the square relating `f`, `tensorQuotEquiv` and the induced maps on the quotients commutes. -/
lemma tensorQuotEquiv_naturality (f : N →ₗ[A ⧸ I] N') :
    (tensorQuotEquiv I N' M).toLinearMap.restrictScalars A ∘ₗ
        LinearMap.rTensor M (f.restrictScalars A)
      = (LinearMap.rTensor (M ⧸ I • (⊤ : Submodule A M)) f).restrictScalars A ∘ₗ
        (tensorQuotEquiv I N M).toLinearMap := by
  apply TensorProduct.ext'
  intro n m
  simp [tensorQuotEquiv_tmul]

end Naturality

end Work.DSM2b
