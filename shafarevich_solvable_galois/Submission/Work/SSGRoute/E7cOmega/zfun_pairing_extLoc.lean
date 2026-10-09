import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E7cOmega.glueSetup
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.e9c_transport_unram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# E7cΩ: the pairing of the orbit-supported class is computed level by level

This file proves `Work.SSGRoute.E7cOmega.zfun_pairing_extLoc`: for the class `zfun k K w M y`
supported on the `Gal(K/k)`-orbit of a place `w` and prescribed at `w` by `y`, the `w'`-component
(at a place `w'` of an `Ω`-level `L ⊇ K` above `w`) of the level pairing with
`h ∈ H¹(Gal(L/k), res M)` is the `D_{w'}`-level pairing of `y` with the restriction of `h` to
`D_{w'}`, along the local units map `K_wˣ → L_{w'}ˣ`.
-/

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place)

noncomputable section

/-- **Level transport of `extLoc` along the idèle level map.**

For `z ∈ Ext^r_{Gal(K/k)}(M, 𝕀_K)` and places `w | u` (`u` of `K`, `w` of `L`), the `w`-component
of the pushed class `(extRes (galRes k K L) z) ≫ idleRepMap k K L` is the image of the `u`-component
of `z` under the restriction `D_w → D_u` and the local coefficient map `K_uˣ → L_wˣ`. -/
theorem extLoc_push_ideleMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (z : Abelian.Ext M (idelesK k K) r)
    (u : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w u)
    (ι : Rep.res (decompKRestrict k K L u w hw) (localUnitsK (k := k) (K := K) u) ⟶
      localUnitsK (k := k) (K := L) w)
    (hι : ∀ y : (NK.GlobalCFT.Place.localField K u)ˣ,
      ι.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w u hw y)) :
    extLoc (k := k) (K := L) w
        ((extRes (galRes k K L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero r))
      = (extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by
  classical
  have hcoeff : Rep.resMap (decompK (k := k) (K := L) w).subtype (idleRepMap k K L) ≫
        NK.HassePrinciple.ideleToLocalUnits k L w
      = Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι :=
    resMap_idleRepMap_comp_ideleToLocalUnits (k := k) (K := K) (L := L) u w hw ι hι
  simp only [extLoc, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rw [ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor (galRes k K L))
        (Rep.resFunctor (decompK (k := k) (K := L) w).subtype) r M
        (Work.SSGRoute.idelesRepP k K) z,
    ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor (decompK (k := k) (K := K) u).subtype)
        (Rep.resFunctor (decompKRestrict k K L u w hw)) r M (Work.SSGRoute.idelesRepP k K) z,
    hcoeff]
  have hfun : Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (galRes k K L) ⋙
          Rep.resFunctor (decompK (k := k) (K := L) w).subtype) z
      = Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (decompK (k := k) (K := K) u).subtype ⋙
          Rep.resFunctor (decompKRestrict k K L u w hw)) z := rfl
  rw [hfun]

theorem zfun_pairing_extLoc {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place ↥L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1) :
    SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w'
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K ↥L)
          (Work.SSGRoute.idleRepMap k K ↥L) (Work.SSGRoute.E7cOmega.zfun k K w M y) h)
      = SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K ↥L w w' hw')
          (Work.SSGRoute.localUnitsMap k K ↥L w w' hw') y
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w') h) := by
  rw [Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥L) M
      (zfun k K w M y) h w']
  rw [extLoc_push_ideleMap (k := k) (K := K) (L := ↥L) (z := zfun k K w M y) w w' hw'
      (localUnitsMap k K ↥L w w' hw') (localUnitsMap_spec k K ↥L w w' hw')]
  rw [zfun_extLoc_w]
  rfl

end

end Work.SSGRoute.E7cOmega
