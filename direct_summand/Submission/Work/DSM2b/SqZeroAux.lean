import Mathlib

/-!
# Square-zero descent for flatness — auxiliary definitions

This file sets up the vocabulary used in the proof of
`Work.DSM2b.flat_of_flat_mod_sqZero`.  Throughout, `A` is a commutative ring, `I ⊆ A` an ideal
(with `I ^ 2 = ⊥` in the applications), `M` an `A`-module and `N := M ⧸ I • ⊤`.

The structural objects are

* `idealQuotImage I J` : the image of an ideal `J` of `A` in `A ⧸ I`, viewed as a submodule of the
  `A`-module `A ⧸ I`.  It carries both an `A`-module structure (as a submodule) and an `A ⧸ I`-module
  structure (because `I` kills it), which are compatible.
* `theta I J N` : the "action" map `↥(idealQuotImage I J) ⊗[A ⧸ I] N → N`, which is injective when
  `N` is flat over `A ⧸ I`.

The main results are `theta_injective` and the exactness statements
`exact_inclusion_idealQuotImageMap` / `exact_rTensor_inclusion_idealQuotImageMap`.
-/

namespace Work.DSM2b

open scoped TensorProduct
open LinearMap (lsmul)

universe u

variable {A : Type u} [CommRing A]

/-- The image of the ideal `J` in `A ⧸ I`, as a submodule of the `A`-module `A ⧸ I`. -/
abbrev idealQuotImage (I J : Ideal A) : Submodule A (A ⧸ I) :=
  Submodule.map (Submodule.mkQ I) J

/-- The natural surjection `J → A ⧸ I`, with image `idealQuotImage I J`. -/
def idealQuotImageMap (I J : Ideal A) : ↥J →ₗ[A] idealQuotImage I J where
  toFun x := ⟨Submodule.mkQ I (x : A), Submodule.mem_map_of_mem x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.mkQ_apply, map_add]
  map_smul' a x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
    rfl

@[simp]
lemma idealQuotImageMap_apply (I J : Ideal A) (x : ↥J) :
    ((idealQuotImageMap I J x : idealQuotImage I J) : A ⧸ I) = Submodule.mkQ I (x : A) := rfl

lemma idealQuotImageMap_eq_zero_iff (I J : Ideal A) (x : ↥J) :
    idealQuotImageMap I J x = 0 ↔ (x : A) ∈ I := by
  constructor
  · intro h
    have h' : Submodule.Quotient.mk (p := I) (x : A) = 0 := by
      simpa [Submodule.mkQ_apply] using congrArg Subtype.val h
    exact (Submodule.Quotient.mk_eq_zero I).mp h'
  · intro h
    apply Subtype.ext
    simp only [Submodule.coe_zero, idealQuotImageMap_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero I).mpr h

lemma surjective_algebraMap_quot (I : Ideal A) :
    Function.Surjective (algebraMap A (A ⧸ I)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- `I` kills the image of any ideal in `A ⧸ I`. -/
lemma isTorsionBySet_idealQuotImage (I J : Ideal A) :
    Module.IsTorsionBySet A ↥(idealQuotImage I J) I := by
  intro x a
  obtain ⟨j, hj, hjx⟩ := (Submodule.mem_map (p := J) (f := Submodule.mkQ I)).mp x.2
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  rw [← hjx, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right (I := I) j a.2

instance instModuleIdealQuotImage (I J : Ideal A) : Module (A ⧸ I) ↥(idealQuotImage I J) :=
  (isTorsionBySet_idealQuotImage I J).module

instance instIsScalarTowerIdealQuotImage (I J : Ideal A) :
    IsScalarTower A (A ⧸ I) ↥(idealQuotImage I J) :=
  Module.IsTorsionBySet.isScalarTower (isTorsionBySet_idealQuotImage I J)

@[simp]
lemma idealQuotImage_mk_smul (I J : Ideal A) (a : A) (x : ↥(idealQuotImage I J)) :
    Ideal.Quotient.mk I a • x = a • x :=
  Module.IsTorsionBySet.mk_smul (isTorsionBySet_idealQuotImage I J) a x

/-- The inclusion `↥(idealQuotImage I J) → A ⧸ I`, as an `A ⧸ I`-linear map (the underlying
function is the coercion). -/
noncomputable def quotImageSubtype (I J : Ideal A) : ↥(idealQuotImage I J) →ₗ[A ⧸ I] A ⧸ I :=
  (Submodule.subtype (idealQuotImage I J)).extendScalarsOfSurjective (surjective_algebraMap_quot I)

@[simp]
lemma quotImageSubtype_apply (I J : Ideal A) (x : ↥(idealQuotImage I J)) :
    quotImageSubtype I J x = (x : A ⧸ I) := by
  rw [quotImageSubtype, LinearMap.extendScalarsOfSurjective_apply]
  rfl

lemma quotImageSubtype_injective (I J : Ideal A) : Function.Injective (quotImageSubtype I J) :=
  fun x y h => Subtype.ext (by simpa using h)

/-- The action map `↥(idealQuotImage I J) ⊗[A ⧸ I] N → N`, `x ⊗ n ↦ x • n`. -/
noncomputable def theta (I J : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] :
    ↥(idealQuotImage I J) ⊗[A ⧸ I] N →ₗ[A ⧸ I] N :=
  TensorProduct.lift ((lsmul (A ⧸ I) N).comp (quotImageSubtype I J))

@[simp]
lemma theta_tmul (I J : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N]
    (x : ↥(idealQuotImage I J)) (n : N) : theta I J N (x ⊗ₜ n) = (x : A ⧸ I) • n := by
  rw [theta, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply,
    quotImageSubtype_apply]

/-- The action map on an ideal quotient is injective when `N` is flat over `A ⧸ I`. -/
lemma theta_injective (I J : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] (hN : Module.Flat (A ⧸ I) N) :
    Function.Injective (theta I J N) := by
  have hcomp : (theta I J N) =
      (TensorProduct.lid (A ⧸ I) N).toLinearMap ∘ₗ
        LinearMap.rTensor N (quotImageSubtype I J) := by
    apply TensorProduct.ext'
    intro x n
    simp only [theta_tmul, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      quotImageSubtype_apply]
  rw [hcomp]
  exact (TensorProduct.lid (A ⧸ I) N).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (quotImageSubtype I J)
      (quotImageSubtype_injective I J))

/-- The kernel of `idealQuotImageMap` is the intersection with `I`. -/
lemma exact_inclusion_idealQuotImageMap (I J : Ideal A) :
    Function.Exact (Submodule.inclusion (inf_le_left : J ⊓ I ≤ J)) (idealQuotImageMap I J) := by
  rw [LinearMap.exact_iff]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    exact ⟨⟨x, ⟨x.2, (idealQuotImageMap_eq_zero_iff I J x).mp hx⟩⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (idealQuotImageMap_eq_zero_iff I J ⟨y, y.2.1⟩).mpr y.2.2

section CancelIso

/-- If `P` and `N` are both `A ⧸ I`-modules (with compatible `A`-module structures), then the
`A ⧸ I`-action can be moved across the tensor product over `A`. -/
theorem compatibleSMul_quot_action (I : Ideal A) {P N : Type u} [AddCommGroup P] [Module A P]
    [Module (A ⧸ I) P] [IsScalarTower A (A ⧸ I) P] [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] :
    TensorProduct.CompatibleSMul A (A ⧸ I) P N := by
  refine ⟨fun b p n => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq I, IsScalarTower.algebraMap_smul (A ⧸ I) a p,
    IsScalarTower.algebraMap_smul (A ⧸ I) a n]
  exact TensorProduct.smul_tmul a p n

/-- If `P` and `N` are both `A ⧸ I`-modules (with compatible `A`-module structures), then the
`A`-action can be moved across the tensor product over `A ⧸ I`. -/
theorem compatibleSMul_action_quot (I : Ideal A) {P N : Type u} [AddCommGroup P] [Module A P]
    [Module (A ⧸ I) P] [IsScalarTower A (A ⧸ I) P] [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] :
    TensorProduct.CompatibleSMul (A ⧸ I) A P N := by
  refine ⟨fun a p n => ?_⟩
  rw [← IsScalarTower.algebraMap_smul (A ⧸ I) a p, ← IsScalarTower.algebraMap_smul (A ⧸ I) a n]
  exact TensorProduct.smul_tmul (algebraMap A (A ⧸ I) a) p n

/-- **Cancellation of base change.** If `P` and `N` are `A ⧸ I`-modules (with compatible
`A`-module structures), then `P ⊗[A] N ≃ P ⊗[A ⧸ I] N`, the map being `p ⊗ n ↦ p ⊗ n`. -/
noncomputable def tensorCancelIso (I : Ideal A) (P N : Type u) [AddCommGroup P] [Module A P]
    [Module (A ⧸ I) P] [IsScalarTower A (A ⧸ I) P] [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] :
    P ⊗[A] N ≃ₗ[A] P ⊗[A ⧸ I] N := by
  haveI : TensorProduct.CompatibleSMul A (A ⧸ I) P N := compatibleSMul_quot_action I
  haveI : TensorProduct.CompatibleSMul (A ⧸ I) A P N := compatibleSMul_action_quot I
  exact TensorProduct.equivOfCompatibleSMul (A ⧸ I) A A P N

@[simp]
lemma tensorCancelIso_tmul (I : Ideal A) (P N : Type u) [AddCommGroup P] [Module A P]
    [Module (A ⧸ I) P] [IsScalarTower A (A ⧸ I) P] [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] (p : P) (n : N) :
    tensorCancelIso I P N (p ⊗ₜ[A] n) = p ⊗ₜ[A ⧸ I] n :=
  rfl

@[simp]
lemma tensorCancelIso_symm_tmul (I : Ideal A) (P N : Type u) [AddCommGroup P] [Module A P]
    [Module (A ⧸ I) P] [IsScalarTower A (A ⧸ I) P] [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N] (p : P) (n : N) :
    (tensorCancelIso I P N).symm (p ⊗ₜ[A ⧸ I] n) = p ⊗ₜ[A] n :=
  rfl

end CancelIso

/-- Right exactness of the tensor product applied to the sequence `J ⊓ I → J → A ⧸ I`. -/
lemma exact_rTensor_inclusion_idealQuotImageMap (I J : Ideal A) (N : Type u) [AddCommGroup N]
    [Module A N] :
    Function.Exact (LinearMap.rTensor N (Submodule.inclusion (inf_le_left : J ⊓ I ≤ J)))
      (LinearMap.rTensor N (idealQuotImageMap I J)) := by
  have hsurj : Function.Surjective (idealQuotImageMap I J) := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hyx⟩ := (Submodule.mem_map (p := J) (f := Submodule.mkQ I)).mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  exact rTensor_exact N (exact_inclusion_idealQuotImageMap I J) hsurj

end Work.DSM2b
