import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.phi1_level_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7cΩ: shared definitions and level glue for the assembly of
`Work.SSGRoute.local_phi_realization_in`

This file collects the vocabulary of the E7cΩ assembly, so that the individual pieces of the
argument can be stated and proved in parallel:

* `Work.SSGRoute.localUnitsMap` — the chosen `D_u`-equivariant local units map `K_wˣ ⟶ L_uˣ` of a
  level pair `k ⊆ K ⊆ L` with places `w | u`, together with its computation rule
  (`localUnitsMap_spec`) and the uniqueness statement (`localUnitsMap_ext`) which lets two such maps
  defined by different (composite) descriptions be identified.
* `Work.SSGRoute.extToClasses_sub` — additivity of the push-forward `𝕀_L → C_L`.
* `Work.SSGRoute.level_sup_instances` — the compositum `L ⊔ L'` of two `Ω`-levels is again a level
  (`NumberField`, `FiniteDimensional k`, `IsGalois k`).
* `Work.SSGRoute.exists_place_under` — a place of a level below a place of a larger level.
-/

open SSGRoute.PTExt CategoryTheory

noncomputable section

namespace Work.SSGRoute

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-! ## The local units map of a level pair -/

/-- **The local units map at a level pair.**  For a tower `k ⊆ K ⊆ L` of number fields with `L/k`,
`K/k` finite Galois and places `w | u` of `L | K`, this is the `D_w`-equivariant morphism of local
unit groups `K_uˣ ⟶ L_wˣ` induced by the completion of the inclusion `K → L`
(`Work.SSGRoute.localUnitsMap_exists`).  It is chosen once and for all; `localUnitsMap_ext` shows
that any other morphism with the same computation rule on `Additive.ofMul` agrees with it. -/
def localUnitsMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (u : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w u) :
    Rep.res (decompKRestrict k K L u w hw) (localUnitsK (k := k) (K := K) u) ⟶
      NK.HassePrinciple.localUnitsRep k L w :=
  (localUnitsMap_exists k K L u w hw (decompKRestrict k K L u w hw)
    (fun σ => decompKRestrict_coe k K L u w hw σ)).choose

/-- The computation rule of `localUnitsMap`: it sends `ofMul y` to `ofMul` of the local algebra
map of `y`. -/
theorem localUnitsMap_spec (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (u : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w u) :
    ∀ y : (NK.GlobalCFT.Place.localField K u)ˣ,
      (localUnitsMap k K L u w hw).hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w u hw y) :=
  (localUnitsMap_exists k K L u w hw (decompKRestrict k K L u w hw)
    (fun σ => decompKRestrict_coe k K L u w hw σ)).choose_spec

/-- **Uniqueness of the local units map.**  A morphism of representations out of the restriction of
`K_uˣ` to `D_w` with the computation rule of the local algebra map is `localUnitsMap`. -/
theorem localUnitsMap_ext (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (u : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w u)
    (φ : Rep.res (decompKRestrict k K L u w hw) (localUnitsK (k := k) (K := K) u) ⟶
      NK.HassePrinciple.localUnitsRep k L w)
    (hφ : ∀ y : (NK.GlobalCFT.Place.localField K u)ˣ,
      φ.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w u hw y)) :
    φ = localUnitsMap k K L u w hw := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = x := ⟨Additive.toMul x, rfl⟩
  exact (hφ y).trans (localUnitsMap_spec k K L u w hw y).symm

/-- **`extToClasses` is additive.** -/
theorem extToClasses_sub {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] {M : Rep Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (a b : Abelian.Ext M (idelesK k K) r) :
    extToClasses (a - b) = extToClasses a - extToClasses b := by
  show (a - b).comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero r)
      = a.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero r)
        - b.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero r)
  simp only [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp]

/-! ## Glue for the level poset `L ≤ L'` of `Ω`-levels -/

section SupGlue

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **The compositum of two `Ω`-levels is a level.** -/
theorem level_sup_instances (L L' : IntermediateField K Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L'] :
    NumberField ↥(L ⊔ L') ∧ FiniteDimensional k ↥(L ⊔ L') ∧ IsGalois k ↥(L ⊔ L') := by
  haveI hK : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  haveI hK' : FiniteDimensional K ↥L' := FiniteDimensional.right k K ↥L'
  haveI hsup : FiniteDimensional K ↥(L ⊔ L') :=
    IntermediateField.finiteDimensional_sup L L'
  have hgal : IsGalois k ↥(L ⊔ L') := isGalois_sup (L := L) (L' := L')
  exact ⟨inferInstance, inferInstance, hgal⟩

/-- **A place of a sub-level below a place of the level.**  For an inclusion of number fields
`K ⊆ L` (here: two `Ω`-levels) with `K` a number field, every place of `L` has a place of `K`
below it. -/
theorem exists_place_under {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L'] (u' : NK.GlobalCFT.Place L') :
    ∃ u : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver u' u :=
  NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := L) (L := L') u'

end SupGlue

end Work.SSGRoute
