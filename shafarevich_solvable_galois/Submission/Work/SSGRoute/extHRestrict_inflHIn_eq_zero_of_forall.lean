import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.Sha2Lib.isLocTrivialLevel_inflH
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of the level inflation to a decomposition group

For finite Galois levels `k ⊆ K ⊆ L ⊆ L' ≤ Ω` of a number field `k`, a `Gal(K/k)`-module `M`, and
a place `v` of `K`, if a class `h ∈ H¹(Gal(L/k), res M)` dies on the decomposition group of every
place `w` of `L` above `v`, then its inflation `inflHIn hLL h ∈ H¹(Gal(L'/k), res M)` dies on the
decomposition group of every place `w'` of `L'` above `v`.

The mathematical content is the standard compatibility of inflation with the place-theoretic
restriction of decomposition groups: if `w` is the place of `L` below `w'`, then the restriction
`Gal(L'/k) →* Gal(L/k)` maps `D_{w'} = Gal(L'/k)_{w'}` into `D_w = Gal(L/k)_w`
(`Work.SSGRoute.decompK_restrict_exists`), and

  `res_{D_{w'}} (infl_{L ≤ L'} h) = infl_{D_w ≤ D_{w'}} (res_{D_w} h)`.

The latter is the formal `Ext`-calculus identity `extHRestrict_extHMap_gen` proved below (the
general-coefficient companion of `Work.SSGRoute.Sha2Lib.extHRestrict_extHMap_comp`).

All the ingredients are formal: the functoriality of `Abelian.Ext.mapExactFunctor`, the
associativity of the Yoneda product `Abelian.Ext.comp`, and the place theory
(`NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder`, `Work.SSGRoute.place_liesOver_trans`,
`Work.SSGRoute.decompK_restrict_exists`).  No arithmetic input, no choice beyond the place `w`
below `w'`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

noncomputable section

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

/-! ## Two formal `Ext`-calculus lemmas -/

section Abstract

variable {G H : Type} [Group G] [Group H]

/-- **Change of group homomorphism along an equality, with an arbitrary coefficient map.**  If
`φ = ψ : H →* G` and `ι : Rep.res ψ A ⟶ B`, then inflating along `φ` through the canonical
transport `eqToHom` of the equality of coefficient modules (composed with `ι`) is the same as
inflating along `ψ` through `ι`.  General-coefficient companion of
`Work.SSGRoute.Sha2Lib.extHMap_congr`. -/
theorem extHMap_congr_coeff {φ ψ : H →* G} (h : φ = ψ) {A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res ψ A ⟶ B) {n : ℕ} (y : extH A n) :
    extHMap φ (eqToHom (congrArg (fun t => Rep.res t A) h) ≫ ι) y = extHMap ψ ι y := by
  cases h
  rw [show congrArg (fun t => Rep.res t A) (rfl : φ = φ) = rfl from Subsingleton.elim _ _]
  simp [eqToHom_refl]

/-- **Restriction of a change of group.**  For group homomorphisms `p : G →* H`, a coefficient map
`ε : Rep.res p A ⟶ B`, subgroups `D' ≤ G`, `D ≤ H` such that `p` maps `D'` into `D` (witnessed by
`f : D' →* D` with `p.comp D'.subtype = D.subtype.comp f`), restricting the inflated class
`extHMap p ε y` to `D'` is the inflation along `f` of the restriction of `y` to `D`.

This is the general-coefficient companion of `Work.SSGRoute.Sha2Lib.extHRestrict_extHMap_comp`
(which treats the case `ε = 𝟙`); the extra ingredient is the canonical transport
`eqToHom (congrArg (fun t => Rep.res t A) hf.symm) ≫ Rep.resMap D'.subtype ε` of the coefficient
morphism, whose two sources are definitionally equal (`Rep.resFunctor` is an abbreviation). -/
theorem extHRestrict_extHMap_gen (p : G →* H) {A : Rep.{0} Coeff H} {B : Rep.{0} Coeff G}
    (ε : Rep.res p A ⟶ B) (D' : Subgroup G) (D : Subgroup H) (f : D' →* D)
    (hf : p.comp D'.subtype = D.subtype.comp f) {n : ℕ} (y : extH A n) :
    extHRestrict D' (extHMap p ε y)
      = extHMap f (eqToHom (congrArg (fun t => Rep.res t A) hf.symm) ≫ Rep.resMap D'.subtype ε)
          (extHRestrict D y) := by
  have h1 : extHRestrict D' (extHMap p ε y)
      = extHMap (p.comp D'.subtype)
          (Rep.resMap D'.subtype ε ≫ 𝟙 (Rep.res D'.subtype B)) y := by
    rw [extHRestrict]
    exact extHMap_comp_aux p D'.subtype ε (𝟙 _)
      (Rep.resMap D'.subtype ε ≫ 𝟙 _) (by rw [Category.comp_id]) y
  have h2 : extHMap (p.comp D'.subtype)
        (Rep.resMap D'.subtype ε ≫ 𝟙 (Rep.res D'.subtype B)) y
      = extHMap (D.subtype.comp f)
          (eqToHom (congrArg (fun t => Rep.res t A) hf.symm)
            ≫ (Rep.resMap D'.subtype ε ≫ 𝟙 (Rep.res D'.subtype B))) y :=
    (extHMap_congr_coeff hf.symm (Rep.resMap D'.subtype ε ≫ 𝟙 (Rep.res D'.subtype B)) y).symm
  rw [h1, h2]
  exact (extHMap_comp_aux D.subtype f (𝟙 (Rep.res D.subtype A))
    (eqToHom (congrArg (fun t => Rep.res t A) hf.symm) ≫ Rep.resMap D'.subtype ε)
    (eqToHom (congrArg (fun t => Rep.res t A) hf.symm) ≫ (Rep.resMap D'.subtype ε ≫ 𝟙 _))
    (by rw [show Rep.resMap f (𝟙 (Rep.res D.subtype A)) = 𝟙 (Rep.res f (Rep.res D.subtype A))
        from (Rep.resFunctor f).map_id (Rep.res D.subtype A), Category.id_comp,
        Category.comp_id]) y).symm

end Abstract

/-! ## The main statement -/

theorem extHRestrict_inflHIn_eq_zero_of_forall {k K Ω : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω]
    [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (L L' : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
    (v : NK.GlobalCFT.Place K) (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1)
    (hzero : ∀ w : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w v →
      SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) h = 0) :
    ∀ w' : NK.GlobalCFT.Place L', NK.GlobalCFT.Place.LiesOver w' v →
      SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L' ≃ₐ[k] L') w')
        (SSGRoute.PTExt.inflHIn (k := k) (K := K) hLL h) = 0 := by
  intro w' hw'v
  -- the level inclusion `L ≤ L'` as an algebra structure together with its scalar towers
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  -- the place of `L` below `w'`
  obtain ⟨w, hw'w⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := ↥L) (L := ↥L') w'
  obtain ⟨v', hwv'⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w
  have hv' : v' = v := place_liesOver_unique (K := K) (L := ↥L') w'
    (place_liesOver_trans hw'w hwv') hw'v
  have hwv : NK.GlobalCFT.Place.LiesOver w v := by rw [← hv']; exact hwv'
  -- the restriction of the decomposition groups
  obtain ⟨f, hfσ⟩ := decompK_restrict_exists k ↥L ↥L' w w' hw'w
  have hf : (galRes k ↥L ↥L').comp (MulAction.stabilizer (↥L' ≃ₐ[k] ↥L') w').subtype
      = (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w).subtype.comp f := by
    refine MonoidHom.ext (fun σ => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact (hfσ σ).symm
  -- the formal identity, and the hypothesis at the place `w`
  have key := extHRestrict_extHMap_gen (galRes k ↥L ↥L') (resResHom M)
    (MulAction.stabilizer (↥L' ≃ₐ[k] ↥L') w') (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w) f hf h
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflHLevel]
  rw [key, hzero w hwv]
  exact E6Util.extHMap_zero f _

end Work.SSGRoute
