import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E9c.TransportDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-- **E9c, transport of *vanishing* of a local component along the level map `K → L`.**

Let `k ⊆ K ⊆ L` be a tower of number fields with `L/k` finite Galois, `M` a `Gal(K/k)`-module,
`z ∈ Ext^r_{Gal(K/k)}(M, 𝕀_K)`, `u` a place of `K`, `w` a place of `L` over `u`.  Let
`idleRepMap k K L : res (idelesRepP k K) ⟶ idelesRepP k L` be the idèle map underlying
`classIncl k K L` (`Submission/Work/SSGRoute/E9c/Core.lean`, where `idelesRepP` pins the carrier
universe of `NK.HassePrinciple.ideleRep`).  If the `u`-component of `z` vanishes, then so does the
`w`-component of the pushed class `extRes (galRes k K L) z ≫ φ`.

Route.  Localisation at `w` is `extRes (stabilizer w) (·) ≫ mk₀ (ideleToLocalUnits k L w)`.  The
composite `𝕀_K →^{φ} 𝕀_L →^{eval_w} L_wˣ` is *pointwise* the composite
`𝕀_K →^{eval_u} K_uˣ →^{localAlgebraMapUnits w u hu} L_wˣ` (this is `hφ` of
`Work.SSGRoute.canonicalIdleData`), so at the level of representations over the group
`ρ : stabilizer w →* stabilizer u` (`ρ σ = galRes k K L σ`, which stabilises `u` because `w` lies
over `u`) it factors as `resMap ρ (ideleToLocalUnits k K u) ≫ ψ`.  The res-bookkeeping
(`Abelian.Ext.mapExactFunctor_comp`, `Abelian.Ext.mk₀_comp_mk₀`, `Rep.resMap`,
`Rep.res_obj_ρ`) then gives `extLoc w (pushed z) = (extRes ρ (extLoc u z)) ≫ mk₀ ψ`, which vanishes
when `extLoc u z = 0`. -/
theorem e9c_transport_zero {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext M (Work.SSGRoute.idelesRepP k K) r) (u : Place K) (w : Place L)
    (hw : Place.LiesOver w u)
    (hz : extLoc (k := k) (K := K) u z = 0) :
    extLoc (k := k) (K := L) w
      ((extRes (galRes k K L) z).comp
        (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero r)) = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := localUnitsMap_exists k K L u w hw (decompKRestrict k K L u w hw)
    (fun σ => decompKRestrict_coe k K L u w hw σ)
  have hcoeff : Rep.resMap (decompK (k := k) (K := L) w).subtype (idleRepMap k K L) ≫
        NK.HassePrinciple.ideleToLocalUnits k L w
      = Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ψ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨zz, hzz⟩ : ∃ zz : Idele K, y = Additive.ofMul zz := ⟨Additive.toMul y, rfl⟩
    rw [hzz]
    have hL : (Rep.resMap (decompK (k := k) (K := L) w).subtype (idleRepMap k K L) ≫
        NK.HassePrinciple.ideleToLocalUnits k L w) (Additive.ofMul zz)
        = Additive.ofMul ((canonicalIdleData k K L).φ zz w) :=
      (Rep.comp_apply _ _ _).trans
        ((congrArg (fun t => (NK.HassePrinciple.ideleToLocalUnits k L w) t)
          (show (Rep.resMap (decompK (k := k) (K := L) w).subtype (idleRepMap k K L))
              (Additive.ofMul zz) = Additive.ofMul ((canonicalIdleData k K L).φ zz)
              from rfl)).trans
          (show (NK.HassePrinciple.ideleToLocalUnits k L w)
              (Additive.ofMul ((canonicalIdleData k K L).φ zz))
            = Additive.ofMul ((canonicalIdleData k K L).φ zz w) from rfl))
    have hR : (Rep.resMap (decompKRestrict k K L u w hw)
        (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ψ) (Additive.ofMul zz)
        = Additive.ofMul (Place.localAlgebraMapUnits w u hw (zz u)) :=
      (Rep.comp_apply _ _ _).trans
        ((congrArg (fun t => ψ t)
          (show (Rep.resMap (decompKRestrict k K L u w hw)
              (NK.HassePrinciple.ideleToLocalUnits k K u)) (Additive.ofMul zz)
            = Additive.ofMul (zz u) from rfl)).trans (hψ (zz u)))
    have hX : Additive.ofMul ((canonicalIdleData k K L).φ zz w)
        = Additive.ofMul (Place.localAlgebraMapUnits w u hw (zz u)) := by
      refine congrArg Additive.ofMul ?_
      rw [(canonicalIdleData k K L).hφ zz w]
      have h1 : (canonicalIdleData k K L).u w = u :=
        place_liesOver_unique (w₂ := u) w ((canonicalIdleData k K L).hu w) hw
      have hcast : h1 ▸ (zz ((canonicalIdleData k K L).u w)) = zz u := by cases h1; rfl
      exact (NK.HassePrinciple.localAlgebraMapUnits_cast (K := K) (L := L) w h1
          ((canonicalIdleData k K L).hu w) hw (zz ((canonicalIdleData k K L).u w))).trans
        (congrArg (fun yy => Place.localAlgebraMapUnits w u hw yy) hcast)
    exact hL.trans (hX.trans hR.symm)
  have hmain : extLoc (k := k) (K := L) w
        ((extRes (galRes k K L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero r))
      = (extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z)).comp
          (Abelian.Ext.mk₀ ψ) (add_zero r) := by
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
  rw [hmain, hz]
  simp only [extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp]


end Work.SSGRoute
