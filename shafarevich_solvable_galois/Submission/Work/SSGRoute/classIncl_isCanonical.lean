import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!

# E0c: the inclusion of idèle class groups `C_K → C_L` is a map of `Gal(L/k)`-modules

This is the node `E0c` of the Poitou–Tate `Ext` core (`DESIGN_EXT.md`): the existence of a morphism
of `Gal(L/k)`-representations `res C_K ⟶ C_L` which is induced by an idèle-level map whose
`w`-component is the local embedding `K_{u w}ˣ → L_wˣ`.

The content is that the induced map on idèle class groups, which exists as a group homomorphism
(`NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists`), is automatically
`Gal(L/k)`-*equivariant*: this is the naturality of the idèle inclusion under base change,
`NK.HassePrinciple.ideleInclusion_smul_restrict`. Since the coefficient ring is
`Coeff = ULift ℤ`, the linearity statement is `ℤ`-linearity, i.e. `map_zpow` in multiplicative
notation.

-/

namespace Work.SSGRoute

open SSGRoute.PTExt
open CategoryTheory
open NK.GlobalCFT

/-- A monoid homomorphism, in additive notation: additivity. -/
lemma classIncl_ofMul_monoidHom_add {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (a b : Additive G) :
    Additive.ofMul (ψ (Additive.toMul (a + b))) =
      Additive.ofMul (ψ (Additive.toMul a)) + Additive.ofMul (ψ (Additive.toMul b)) := by
  rw [toMul_add, map_mul, ofMul_mul]

/-- A monoid homomorphism, in additive notation: `Coeff`-linearity, i.e. compatibility with
`zpow`, using that the module structure of the coefficient ring `Coeff = ULift ℤ` is
`n • x = n.down • x`. -/
lemma classIncl_ofMul_monoidHom_smul {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (n : Coeff) (x : Additive G) :
    Additive.ofMul (ψ (Additive.toMul (n • x))) =
      (RingHom.id Coeff) n • Additive.ofMul (ψ (Additive.toMul x)) := by
  change Additive.ofMul (ψ (Additive.toMul ((n.down : ℤ) • x))) =
    n.down • Additive.ofMul (ψ (Additive.toMul x))
  rw [toMul_zsmul, map_zpow, ofMul_zpow]

/-- **E0c.** The inclusion of idèle class groups `C_K → C_L` (induced by the local embeddings
`K_v → L_w`) is a morphism of `Gal(L/k)`-modules, so `classIncl` is the canonical one. -/
theorem classIncl_isCanonical (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L] :
    IsCanonicalClassIncl k K L (classIncl k K L) := by
  classical
  have hfin : FiniteDimensional K L := inferInstance
  -- a choice of base place for every place of `L`
  let u : Place L → Place K :=
    fun w => Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)
  have hu : ∀ w : Place L, Place.LiesOver w (u w) := fun w =>
    Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)
  -- the induced maps on idèles and on idèle class groups
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists u hu
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  -- the induced map on class groups is `Gal(L/k)`-equivariant
  have heq : ∀ (σ : L ≃ₐ[k] L) (y : IdeleClassGroup K), ψ ((galRes k K L σ) • y) = σ • ψ y := by
    intro σ y
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K y
    rw [IdeleClassGroup.smul_mk, hψ (galRes k K L σ • x), hψ x, IdeleClassGroup.smul_mk]
    exact congrArg (IdeleClassGroup.mk L)
      (NK.HassePrinciple.ideleInclusion_smul_restrict (K := k) (F := K) (L := L)
        u hu φ hφ σ x).symm
  -- package `ψ` as a morphism of representations
  let ι : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L :=
    Rep.ofHom { toFun := fun y => Additive.ofMul (ψ (Additive.toMul y)),
                map_add' := fun a b => classIncl_ofMul_monoidHom_add ψ a b
                map_smul' := fun n x => classIncl_ofMul_monoidHom_smul ψ n x
                isIntertwining' := fun σ => by
                  apply LinearMap.ext
                  intro y
                  exact congrArg Additive.ofMul (heq σ (Additive.toMul y)) }
  have hι : ∀ x : Idele K, ι.hom (Additive.ofMul (IdeleClassGroup.mk K x)) =
      Additive.ofMul (IdeleClassGroup.mk L (φ x)) := by
    intro x
    change Additive.ofMul (ψ (Additive.toMul (Additive.ofMul (IdeleClassGroup.mk K x)))) =
      Additive.ofMul (IdeleClassGroup.mk L (φ x))
    rw [toMul_ofMul, hψ x]
  have hex : ∃ ι : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L,
      IsCanonicalClassIncl k K L ι := ⟨ι, u, hu, φ, hφ, hι⟩
  -- `classIncl` is defined by choice out of exactly this existence statement
  rw [classIncl, dif_pos hex]
  exact Classical.choose_spec hex

end Work.SSGRoute
