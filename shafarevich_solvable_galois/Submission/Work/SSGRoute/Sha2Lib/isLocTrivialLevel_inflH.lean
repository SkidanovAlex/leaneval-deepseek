import Mathlib
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.Sha2Lib.LevelLocTrivial
import Submission.Work.SSGRoute.inflTrivIn_trans
import Submission.Work.SSGRoute.e6_util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local triviality is preserved by inflation `H¹(Gal(K/k), M) → H¹(Gal(L/k), M)`

This is Lemma `L2` of the all-levels form of `E9` (`Work.SSGRoute.Sha2Lib._chk_place`): if
`h ∈ H^s(Gal(K/k), M)` is locally trivial at every place of `K` (`SSGRoute.PTExt.IsLocTrivial`),
then its inflation `inflH h ∈ H^s(Gal(L/k), M)` is locally trivial at every place of `L`
(`SSGRoute.PTExt.IsLocTrivialLevel`).

The two ingredients are:

* **Places and decomposition groups.**  Every place `w'` of `L` lies over some place `w` of `K`
  (`NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder`), and the restriction
  `Gal(L/k) →* Gal(K/k)` maps the decomposition group of `w'` into that of `w`
  (`Work.SSGRoute.decompK_restrict_exists`).
* **A formal `Ext`-calculus identity** (`extHRestrict_extHMap_comp`): restricting an inflation
  `extHMap f 𝟙 y` to a subgroup `D ≤ H` whose image under `f` lies in a subgroup `E ≤ G`
  (witnessed by `f' : D →* E` with `f.comp D.subtype = E.subtype.comp f'`) equals the inflation
  along `f'` of the restriction to `E`.

Everything is formal bookkeeping of `Abelian.Ext.mapExactFunctor`, `Abelian.Ext.comp` and the
`Rep.resFunctor` restriction functors; no arithmetic and no choice beyond the place under `w'`.
-/

open CategoryTheory

namespace Work.SSGRoute.Sha2Lib

open SSGRoute.PTExt

/-- **`extHMap` only depends on the presentation of the group homomorphism** (identity coefficient
form).  If `φ ψ : H →* G` are equal group homomorphisms, then the change-of-group maps along `φ`
and along `ψ` agree, the latter with the canonical transport of the coefficient module
`eqToHom (congrArg (fun t => Rep.res t A) h.symm)`. -/
theorem extHMap_congr {G H : Type} [Group G] [Group H] {φ ψ : H →* G} (h : φ = ψ)
    {A : Rep SSGRoute.PTExt.Coeff G} {n : ℕ} (y : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHMap φ (𝟙 (Rep.res φ A)) y
      = SSGRoute.PTExt.extHMap ψ (eqToHom (congrArg (fun t => Rep.res t A) h.symm)) y := by
  cases h
  rw [show (congrArg (fun t => Rep.res t A) (rfl : φ = φ)) = rfl from Subsingleton.elim _ _,
    eqToHom_refl]

/-- **Restriction of an inflation.**  For group homomorphisms `f : H →* G`, a subgroup `D ≤ H`, and
a subgroup `E ≤ G` containing the image of `D` under `f` (witnessed by `f' : D →* E` with
`f.comp D.subtype = E.subtype.comp f'`), restricting the inflated class `extHMap f 𝟙 y` to `D`
is the inflation along `f'` of the restriction of `y` to `E`. -/
theorem extHRestrict_extHMap_comp {G H : Type} [Group G] [Group H]
    (f : H →* G) (D : Subgroup H) (E : Subgroup G) (f' : D →* E)
    (hf : f.comp D.subtype = E.subtype.comp f') {A : Rep SSGRoute.PTExt.Coeff G} {n : ℕ}
    (y : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHRestrict D (SSGRoute.PTExt.extHMap f (𝟙 (Rep.res f A)) y)
      = SSGRoute.PTExt.extHMap f'
          (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))
          (SSGRoute.PTExt.extHRestrict E y) := by
  have hres1 : Rep.resMap D.subtype (𝟙 (Rep.res f A))
      = 𝟙 (Rep.res D.subtype (Rep.res f A)) :=
    (Rep.resFunctor D.subtype).map_id (Rep.res f A)
  have hres2 : Rep.resMap f' (𝟙 (Rep.res E.subtype A))
      = 𝟙 (Rep.res f' (Rep.res E.subtype A)) :=
    (Rep.resFunctor f').map_id (Rep.res E.subtype A)
  simp only [SSGRoute.PTExt.extHRestrict]
  rw [show SSGRoute.PTExt.extHMap D.subtype (𝟙 (Rep.res D.subtype (Rep.res f A)))
        (SSGRoute.PTExt.extHMap f (𝟙 (Rep.res f A)) y)
      = SSGRoute.PTExt.extHMap (f.comp D.subtype)
          (𝟙 (Rep.res D.subtype (Rep.res f A))) y from
      extHMap_comp_aux f D.subtype (𝟙 (Rep.res f A))
        (𝟙 (Rep.res D.subtype (Rep.res f A))) (𝟙 (Rep.res D.subtype (Rep.res f A)))
        (by rw [hres1, Category.id_comp]) y]
  rw [show SSGRoute.PTExt.extHMap f'
        (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))
        (SSGRoute.PTExt.extHMap E.subtype (𝟙 (Rep.res E.subtype A)) y)
      = SSGRoute.PTExt.extHMap (E.subtype.comp f')
          (eqToHom (congrArg (fun t => Rep.res t A) hf.symm)) y from
      extHMap_comp_aux E.subtype f' (𝟙 (Rep.res E.subtype A))
        (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))
        (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))
        (by rw [hres2, Category.id_comp]) y]
  exact extHMap_congr hf y

theorem isLocTrivialLevel_inflH
    (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {s : ℕ}
    (h : SSGRoute.PTExt.extH M s) (hh : SSGRoute.PTExt.IsLocTrivial (k := k) (K := K) h) :
    SSGRoute.PTExt.IsLocTrivialLevel (k := k) (K := K) (L := L)
      (SSGRoute.PTExt.inflH (k := k) (K := K) (L := L) h) := by
  simp only [SSGRoute.PTExt.IsLocTrivialLevel, SSGRoute.PTExt.IsLocTrivial,
    SSGRoute.PTExt.IsLocTrivialOn, SSGRoute.PTExt.inflH] at hh ⊢
  intro w'
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite k K L
  obtain ⟨w, hw⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w'
  obtain ⟨f, hf⟩ := Work.SSGRoute.decompK_restrict_exists k K L w w' hw
  have hfhom : (SSGRoute.PTExt.galRes k K L).comp
          (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype
      = (MulAction.stabilizer (K ≃ₐ[k] K) w).subtype.comp f := by
    refine MonoidHom.ext (fun σ => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact (hf σ).symm
  rw [show SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (SSGRoute.PTExt.extHMap (SSGRoute.PTExt.galRes k K L)
          (𝟙 (Rep.res (SSGRoute.PTExt.galRes k K L) M)) h)
      = SSGRoute.PTExt.extHMap f
          (eqToHom (congrArg (fun t => Rep.res t M) hfhom.symm))
          (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) w) h) from
      extHRestrict_extHMap_comp (SSGRoute.PTExt.galRes k K L)
        (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (MulAction.stabilizer (K ≃ₐ[k] K) w) f hfhom h]
  rw [hh w]
  exact Work.SSGRoute.E6Util.extHMap_zero f _

end Work.SSGRoute.Sha2Lib
