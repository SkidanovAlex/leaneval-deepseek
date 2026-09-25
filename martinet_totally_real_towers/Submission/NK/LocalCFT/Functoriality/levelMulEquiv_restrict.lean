import Mathlib
import Submission.NK.LocalCFT.Basic

/-!
# Functoriality of the Artin reciprocity isomorphism in the level

At a finite abelian level `L ≤ F^{ab}` of a field `F` with Galois extension `F'`, the local
Artin map induces the reciprocity isomorphism
`D.artinLevelMulEquiv L : Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`.

The main result of this file, `levelMulEquiv_restrict`, says that these isomorphisms are
compatible with restriction in the level: for normal levels `L₂ ≤ L₁ ≤ F^{ab}` and `x : Fˣ`, the
image of `x` under the level-`L₁` isomorphism restricts to its image under the level-`L₂`
isomorphism.  The norm-group quotient map appearing on the right is the one induced by the
inclusion `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ` (the first axiom of a class formation,
`NK.LocalReciprocity.normGroup_le_of_tower`).

The mathematical content is entirely "restriction is transitive", isolated as
`levelRestrictLe_comp_levelRestrict`; the rest is the definitional unfolding of the level
isomorphism.  This is the compatibility that lets the level-wise reciprocity isomorphisms be
glued to the canonical Artin map on `F^{ab}`.
-/

open scoped Classical

-- `haveI`/`letI` are required here: the instances below are local, not global.
set_option linter.style.haveILetI false

namespace NK.LocalCFT.Functoriality

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **Transitivity of restriction between levels of `F^{ab}`.**  For normal levels
`L₂ ≤ L₁ ≤ F^{ab}`, restricting an element of `Gal(F^{ab}/F)` to `L₁` and then to `L₂` is the
same as restricting it to `L₂` directly.

This is the transitivity of `AlgEquiv.restrictNormalHom`
(`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`) for the tower of fields
`F ⊆ L₂ ⊆ L₁ ⊆ F^{ab}`, the algebra structure on `↥L₁` over `↥L₂` being the one induced by the
inclusion. -/
theorem levelRestrictLe_comp_levelRestrict
    {L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    [Normal F L₁] [Normal F L₂] (h : L₂ ≤ L₁) (σ : NK.LocalCFT.AbGal F F') :
    NK.LocalCFT.levelRestrictLe h (NK.LocalCFT.levelRestrict L₁ σ) =
      NK.LocalCFT.levelRestrict L₂ σ := by
  letI : Algebra ↥L₂ ↥L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L₂ ↥L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower ↥L₂ ↥L₁ ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  unfold NK.LocalCFT.levelRestrictLe NK.LocalCFT.levelRestrict
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥L₂ ↥L₁ (f := σ)).symm

/-- **Functoriality of the Artin reciprocity isomorphism in the level.**  For normal levels
`L₂ ≤ L₁ ≤ F^{ab}`, the reciprocity isomorphism at level `L₁`, followed by restriction of Galois
groups to `L₂`, agrees with the reciprocity isomorphism at level `L₂` composed with the quotient
map `Fˣ ⧸ N_{L₁/F} L₁ˣ →* Fˣ ⧸ N_{L₂/F} L₂ˣ` induced by `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ`. -/
theorem levelMulEquiv_restrict {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) (h : L₂ ≤ L₁) (x : Fˣ) :
    NK.LocalCFT.levelRestrictLe h (D.artinLevelMulEquiv L₁ h₁ (QuotientGroup.mk x)) =
      D.artinLevelMulEquiv L₂ h₂
        (QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
          (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ)
          ((letI : Algebra ↥L₂ ↥L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
            haveI : IsScalarTower F ↥L₂ ↥L₁ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
            NK.LocalReciprocity.normGroup_le_of_tower))
          (QuotientGroup.mk x)) := by
  -- The norm-group quotient map sends the class of `x` to the class of `x`.
  have hmap : ∀ (hle : NK.LocalReciprocity.normGroup F ↥L₁ ≤
      NK.LocalReciprocity.normGroup F ↥L₂),
      QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
        (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ) hle (QuotientGroup.mk x) =
        QuotientGroup.mk x := by
    intro hle
    exact QuotientGroup.map_mk _ _ _ hle x
  simp only [hmap]
  -- Both sides are the image of `x` under `artin`, restricted to `L₁` resp. `L₂`.
  rw [NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv_mk,
    NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv_mk]
  exact levelRestrictLe_comp_levelRestrict h (D.artin x)

end NK.LocalCFT.Functoriality
