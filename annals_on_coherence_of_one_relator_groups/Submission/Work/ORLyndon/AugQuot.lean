import Mathlib
import Submission.Work.ORLyndon.Augmentation

/-!
# The augmentation of the quotient `K[G] ⧸ I_{K[G]}`

For a field `K` and a group `G`, the augmentation `ε : K[G] → K` kills the augmentation ideal
`I = I_{K[G]}`, hence induces a `K`-algebra homomorphism `K[G] ⧸ I → K`, which is in fact an
isomorphism (the trivial `K[G]`-module is a quotient of the group algebra by the augmentation
ideal).  This file provides this map `Work.ORLyndon.augQuot` and its basic properties.

## Main definitions

* `Work.ORLyndon.augQuotHom`: the `K`-algebra homomorphism `K[G] ⧸ I →ₐ[K] K`.
* `Work.ORLyndon.augQuot`: the same map, as a `K`-linear map.

## Main results

* `Work.ORLyndon.augQuot_mk`: `augQuot (x + I) = ε x`.
* `Work.ORLyndon.augQuotHom_injective`, `Work.ORLyndon.augQuotHom_surjective`: `augQuotHom` is an
  isomorphism.
* `Work.ORLyndon.smul_mk_augIdeal`: the `K[G]`-action on `K[G] ⧸ I` is multiplication.
-/

set_option autoImplicit false

namespace Work.ORLyndon

universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G]

/-- The augmentation ideal of a group algebra is a two-sided ideal (it is the kernel of the
augmentation). -/
instance instIsTwoSidedAugIdeal (K : Type v) [Field K] (G : Type u) [Group G] :
    (augIdeal K G).IsTwoSided :=
  ⟨fun b ha => by
    rw [mem_augIdeal] at ha ⊢
    rw [augmentation_mul, ha, zero_mul]⟩

/-- The augmentation `ε : K[G] → K` is surjective. -/
theorem augmentation_surjective (K : Type v) [Field K] (G : Type u) [Group G] :
    Function.Surjective (augmentation K G) :=
  fun c => ⟨algebraMap K (MonoidAlgebra K G) c, by
    rw [AlgHom.commutes]
    simp⟩

/-- The augmentation as a `K`-algebra homomorphism on the quotient `K[G] ⧸ I_{K[G]}`. -/
noncomputable def augQuotHom (K : Type v) [Field K] (G : Type u) [Group G] :
    (MonoidAlgebra K G ⧸ augIdeal K G) →ₐ[K] K :=
  (Ideal.quotientKerAlgEquivOfSurjective (f := augmentation K G)
    (augmentation_surjective K G)).toAlgHom

theorem augQuotHom_mk (K : Type v) [Field K] (G : Type u) [Group G]
    (x : MonoidAlgebra K G) :
    augQuotHom K G (Ideal.Quotient.mk (augIdeal K G) x) = augmentation K G x :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ x

theorem augQuotHom_injective (K : Type v) [Field K] (G : Type u) [Group G] :
    Function.Injective (augQuotHom K G) :=
  (Ideal.quotientKerAlgEquivOfSurjective (f := augmentation K G)
    (augmentation_surjective K G)).injective

/-- The augmentation as a `K`-linear map on the quotient `K[G] ⧸ I_{K[G]}`. -/
noncomputable def augQuot (K : Type v) [Field K] (G : Type u) [Group G] :
    (MonoidAlgebra K G ⧸ augIdeal K G) →ₗ[K] K :=
  (augQuotHom K G).toLinearMap

@[simp] theorem augQuot_mk (K : Type v) [Field K] (G : Type u) [Group G]
    (x : MonoidAlgebra K G) :
    augQuot K G (Ideal.Quotient.mk (augIdeal K G) x) = augmentation K G x := by
  rw [augQuot, AlgHom.toLinearMap_apply, augQuotHom_mk]

@[simp] theorem augQuot_one (K : Type v) [Field K] (G : Type u) [Group G] :
    augQuot K G (1 : MonoidAlgebra K G ⧸ augIdeal K G) = 1 := by
  have h : (1 : MonoidAlgebra K G ⧸ augIdeal K G)
      = Ideal.Quotient.mk (augIdeal K G) (1 : MonoidAlgebra K G) :=
    (map_one (Ideal.Quotient.mk (augIdeal K G))).symm
  rw [h, augQuot_mk, augmentation_one]

/-- The `K[G]`-module structure on the quotient is given by multiplication. -/
theorem smul_mk_augIdeal (K : Type v) [Field K] (G : Type u) [Group G]
    (a x : MonoidAlgebra K G) :
    a • Ideal.Quotient.mk (augIdeal K G) x
      = Ideal.Quotient.mk (augIdeal K G) (a * x) := by
  have h : a • (Submodule.Quotient.mk x : MonoidAlgebra K G ⧸ augIdeal K G)
      = Submodule.Quotient.mk (a * x) := by
    rw [← Submodule.Quotient.mk_smul (augIdeal K G : Submodule (MonoidAlgebra K G)
      (MonoidAlgebra K G)) a x, smul_eq_mul]
  simpa only [Ideal.Quotient.mk_eq_mk] using h

end Work.ORLyndon
