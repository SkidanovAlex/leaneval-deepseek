import Mathlib
import Submission.Work.ORDunwoody.FP2

/-!
# `AbelianizationTensorVanishes` is stable under quotients

If `f : G →* H` is a surjective group homomorphism, then `H₁(-;k)` of `H` is a quotient
of `H₁(-;k)` of `G`: the epimorphism `f` induces a surjection of abelianizations
`Abelianization G →* Abelianization H`, hence (by right exactness of `- ⊗ ℤ k`) a surjection
of `k`-modules `H₁(G;k) → H₁(H;k)`.  A quotient of the zero module is zero, so
`H₁(H;k) = 0` whenever `H₁(G;k) = 0`.
-/

set_option autoImplicit false

namespace Work.ORDunwoody.Lemmas

open scoped TensorProduct

open Work.ORDunwoody

/-- The map `Abelianization.map f` induced by a surjective homomorphism `f` is surjective. -/
private theorem abelianization_map_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨a, rfl⟩ := Quotient.exists_rep y
  obtain ⟨x, rfl⟩ := hf a
  exact ⟨Abelianization.of x, rfl⟩

/-- The ℤ-linear map on abelianizations induced by a surjective homomorphism is surjective. -/
private theorem abelianizationIntLinearMap_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective
      (AddMonoidHom.toIntLinearMap
        (MonoidHom.toAdditive (Abelianization.map f)) :
        Additive (Abelianization G) →ₗ[ℤ] Additive (Abelianization H)) :=
  abelianization_map_surjective f hf

/-- If `f : G →* H` is surjective, then `H₁(H;k)` is a quotient of `H₁(G;k)`; in particular
`H₁(G;k) = 0` forces `H₁(H;k) = 0`. -/
theorem abelianizationTensorVanishes_of_surjective {k : Type*} [CommRing k] {G H : Type*}
    [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f)
    (h : AbelianizationTensorVanishes k G) : AbelianizationTensorVanishes k H := by
  let g : Additive (Abelianization G) →ₗ[ℤ] Additive (Abelianization H) :=
    AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map f))
  have hg : Function.Surjective g := abelianizationIntLinearMap_surjective f hf
  exact @Function.Surjective.subsingleton
    (TensorProduct ℤ (Additive (Abelianization G)) k)
    (TensorProduct ℤ (Additive (Abelianization H)) k)
    (LinearMap.rTensor k g) h (LinearMap.rTensor_surjective k hg)

end Work.ORDunwoody.Lemmas
