import Mathlib

/-!
# The compositum of two abelian Galois extensions is abelian

If `E₁` and `E₂` are finite Galois extensions of a field `K` whose Galois groups are
commutative, then their compositum `E₁ ⊔ E₂` again has a commutative Galois group over `K`.

This is a standard ingredient in the theory of abelian extensions and is used in the
proof of Shafarevich's theorem on solvable Galois groups (via the closure properties of the
class of abelian extensions).

The argument does not use the Galois-ness of the compositum; it only uses that the restrictions
`Gal(E₁ ⊔ E₂ / K) → Gal(Eᵢ / K)` are defined (the `Eᵢ` being normal over `K`) and that an
automorphism of the compositum is determined by its restrictions to `E₁` and `E₂`. Hence
`Gal(E₁ ⊔ E₂ / K)` embeds into `Gal(E₁ / K) × Gal(E₂ / K)`, a product of commutative groups.

-/

namespace Work.SSGRoute.myv2

open IntermediateField

set_option linter.style.haveILetI false in
/-- If `f : G →* G₁` and `g : G →* G₂` combine into an injective map `G → G₁ × G₂` and both
`G₁` and `G₂` are commutative, then `G` is commutative. -/
private lemma isMulCommutative_of_injective_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    [IsMulCommutative G₁] [IsMulCommutative G₂] (f : G →* G₁) (g : G →* G₂)
    (h : Function.Injective (f.prod g)) : IsMulCommutative G := by
  refine IsMulCommutative.of_comm fun σ τ => ?_
  apply h
  rw [map_mul, map_mul]
  exact mul_comm' _ _

set_option linter.style.haveILetI false in
theorem sup_isMulCommutative {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (E₁ E₂ : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K E₁] [IsGalois ↥K E₁]
    [FiniteDimensional ↥K E₂] [IsGalois ↥K E₂]
    [IsMulCommutative (↥E₁ ≃ₐ[↥K] ↥E₁)] [IsMulCommutative (↥E₂ ≃ₐ[↥K] ↥E₂)] :
    IsMulCommutative (↥(E₁ ⊔ E₂) ≃ₐ[↥K] ↥(E₁ ⊔ E₂)) := by
  -- The two hypotheses say exactly that `E₁` and `E₂` are abelian (Galois) extensions of `↥K`.
  haveI hab₁ : IsAbelianGalois ↥K ↥E₁ := ⟨⟩
  haveI hab₂ : IsAbelianGalois ↥K ↥E₂ := ⟨⟩
  have hle₁ : E₁ ≤ E₁ ⊔ E₂ := le_sup_left
  have hle₂ : E₂ ≤ E₁ ⊔ E₂ := le_sup_right
  -- View `E₁` and `E₂` as intermediate fields of the compositum `E₁ ⊔ E₂`.
  -- The restricted fields are again abelian Galois over `↥K`.
  haveI : IsAbelianGalois ↥K ↥(E₁.restrict hle₁) :=
    IsAbelianGalois.of_algHom (M := ↥E₁)
      ((IntermediateField.restrictAlgEquiv hle₁).symm.toAlgHom)
  haveI : IsAbelianGalois ↥K ↥(E₂.restrict hle₂) :=
    IsAbelianGalois.of_algHom (M := ↥E₂)
      ((IntermediateField.restrictAlgEquiv hle₂).symm.toAlgHom)
  haveI : IsGalois ↥K ↥(E₁.restrict hle₁) :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv hle₁)
  haveI : IsGalois ↥K ↥(E₂.restrict hle₂) :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv hle₂)
  -- The two restricted fields generate the compositum.
  have hsup : E₁.restrict hle₁ ⊔ E₂.restrict hle₂ = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict hle₁, IntermediateField.lift_restrict hle₂]
  -- The product of the two restriction maps is injective: an automorphism acting trivially on
  -- both `E₁` and `E₂` acts trivially on their compositum.
  have hinj : Function.Injective
      ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥(E₁ ⊔ E₂)) (E₁.restrict hle₁)).prod
       (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥(E₁ ⊔ E₂)) (E₂.restrict hle₂))) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod,
      IntermediateField.restrictNormalHom_ker, IntermediateField.restrictNormalHom_ker,
      ← IntermediateField.fixingSubgroup_sup, hsup, IntermediateField.fixingSubgroup_top]
  -- `Gal(E₁ ⊔ E₂ / K)` embeds into the product of two commutative groups, hence is commutative.
  exact isMulCommutative_of_injective_prod _ _ hinj

end Work.SSGRoute.myv2
