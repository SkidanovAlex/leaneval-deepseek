import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open IntermediateField

/-- The compositum of two abelian (finite Galois) extensions is again abelian Galois.

The Galois group of the compositum `E₁ ⊔ E₂` maps injectively into the product
`Gal(E₁/F) × Gal(E₂/F)` by restricting an automorphism to `E₁` and to `E₂`
(the restriction is well defined because both subextensions are normal).  A subgroup
of an abelian group is abelian, so the Galois group of the compositum is commutative. -/
theorem oddLevel_sup_comm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (E₁ E₂ : IntermediateField F Ω) [FiniteDimensional F ↥E₁] [FiniteDimensional F ↥E₂]
    [IsGalois F ↥E₁] [IsGalois F ↥E₂]
    (h₁ : ∀ a b : ↥E₁ ≃ₐ[F] ↥E₁, a * b = b * a)
    (h₂ : ∀ a b : ↥E₂ ≃ₐ[F] ↥E₂, a * b = b * a) :
    ∀ a b : ↥(E₁ ⊔ E₂) ≃ₐ[F] ↥(E₁ ⊔ E₂), a * b = b * a := by
  intro a b
  -- Write `M` for the compositum and view `E₁`, `E₂` inside it.
  let M : IntermediateField F Ω := E₁ ⊔ E₂
  let E₁' : IntermediateField F ↥M := E₁.restrict le_sup_left
  let E₂' : IntermediateField F ↥M := E₂.restrict le_sup_right
  -- Both subextensions stay Galois (hence normal) after restriction to `M`.
  have hg₁ : IsGalois F ↥E₁' := IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv le_sup_left)
  have hg₂ : IsGalois F ↥E₂' := IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv le_sup_right)
  -- Their Galois groups are abelian, transported along the restriction isomorphisms.
  have comm₁' : ∀ x y : ↥E₁' ≃ₐ[F] ↥E₁', x * y = y * x := by
    intro x y
    refine (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv le_sup_left).symm).injective ?_
    rw [map_mul, map_mul, h₁]
  have comm₂' : ∀ x y : ↥E₂' ≃ₐ[F] ↥E₂', x * y = y * x := by
    intro x y
    refine (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv le_sup_right).symm).injective ?_
    rw [map_mul, map_mul, h₂]
  -- The two restricted subextensions together generate `M`.
  have hEsup : E₁' ⊔ E₂' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict le_sup_left, lift_restrict le_sup_right]
  -- The pair of restriction maps, as a single homomorphism into an abelian product.
  let ρ : (↥M ≃ₐ[F] ↥M) →* (↥E₁' ≃ₐ[F] ↥E₁') × (↥E₂' ≃ₐ[F] ↥E₂') :=
    (AlgEquiv.restrictNormalHom ↥E₁').prod (AlgEquiv.restrictNormalHom ↥E₂')
  -- It is injective: an automorphism of `M` fixing `E₁'` and `E₂'` pointwise is the identity.
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker,
      IntermediateField.restrictNormalHom_ker, ← IntermediateField.fixingSubgroup_sup, hEsup,
      IntermediateField.fixingSubgroup_top]
  -- Therefore commutativity can be checked after applying `ρ`.
  refine hinj ?_
  rw [map_mul, map_mul]
  exact Prod.ext (comm₁' _ _) (comm₂' _ _)

end Work.SSGRoute.ZDataMup
