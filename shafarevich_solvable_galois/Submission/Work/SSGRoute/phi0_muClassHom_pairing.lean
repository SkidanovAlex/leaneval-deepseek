import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.zeta_idele_class_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped RestrictedProduct
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-- **R2 with the explicit `μ_p`-idèle class.**  This is the statement of `Work.SSGRoute.zeta_idele_class_pairing` with the existential class `c₀` replaced by its explicit witness `muClassHom p k K ζ hζ a ha` (the class of the idèle `(ζ^{a w})_w`): the level value of the pairing is the image under `𝕀_L → C_L` of a class whose `w'`-component is `a w • loc_{w'}(κ_L h)`.  The proof of `zeta_idele_class_pairing` already establishes exactly this (`refine ⟨muClassHom p k K ζ hζ a ha, ?_⟩`, followed by the same ~180-line argument); only the exported statement hides the witness, so copy that proof body. -/
theorem phi0_muClassHom_pairing (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (a : NK.GlobalCFT.Place K → ZMod p) (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (z : Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ SSGRoute.PTExt.unitsK k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (h : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) 2) :
    ∃ y : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2,
      (∀ (w' : NK.GlobalCFT.Place L) (w : NK.GlobalCFT.Place K),
        NK.GlobalCFT.Place.LiesOver w' w →
        (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') y).comp
            (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w'))
            (add_zero 2) =
          (a w).val • (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
              (h.comp (CategoryTheory.Abelian.Ext.mk₀ z) (add_zero 2))).comp
            (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w'))
            (add_zero 2)) ∧
      SSGRoute.PTExt.phiTriv (k := k) (K := K) (L := L) (ZMod p)
          (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.muClassHom p k K ζ hζ a ha)) h =
        y.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L))
          (add_zero 2) := by
  classical
  -- the canonical idèle-level inclusion `𝕀_K → 𝕀_L` underlying `classIncl k K L`
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k K L
  let eK : Idele K := muIdeles p k K ζ hζ a
  let eL : Idele L := φ eK
  have heK_pow : eK ^ p = 1 := muIdeles_pow p k K ζ hζ a
  have heL_pow : eL ^ p = 1 := by
    rw [show eL = φ eK from rfl, ← map_pow, heK_pow, map_one]
  haveI : FiniteDimensional K L := NK.GlobalCFT.Inclusion.globalCFT_finiteDimensional_of_numberField
  -- `eL` is fixed by `Gal(L/k)`
  have hgal : ∀ σ : L ≃ₐ[k] L, σ • eL = eL := by
    intro σ
    have h1 : σ • φ eK = φ ((AlgEquiv.restrictNormalHom K σ) • eK) :=
      NK.HassePrinciple.ideleInclusion_smul_of_restrict (K := k) (F := K) (L := L) u hu φ hφ σ eK
    rw [show eL = φ eK from rfl, h1]
    congr 1
    exact muIdeles_smul p k K ζ hζ a ha (AlgEquiv.restrictNormalHom K σ)
  have heL_tor : (p : ℤ) • Additive.ofMul eL = 0 := by
    rw [natCast_zsmul, ← ofMul_pow, heL_pow]
    rfl
  have hfix : ∀ σ : L ≃ₐ[k] L, σ • Additive.ofMul eL = Additive.ofMul eL := by
    intro σ
    show Additive.ofMul (σ • eL) = Additive.ofMul eL
    rw [hgal σ]
  -- the `𝔽_p → 𝕀_L` coefficient morphism of the idèle class `[eL]`
  let ψ : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ idelesK k L :=
    zmodToIdelesRep p k L eL heL_tor hfix
  refine ⟨h.comp (Abelian.Ext.mk₀ ψ) (add_zero 2), ?_, ?_⟩
  · -- local components
    intro w' w hw
    have huw : u w' = w := NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu w') hw
    -- the `w'`-component of `eL` is `ζ^{a w}`
    have hcomp : eL w' = (NK.HassePrinciple.unitsToLocalUnitsHom w'
        (zetaUnitK p k L ζ hζ)) ^ (a w).val := by
      have key : eL w' = (NK.HassePrinciple.unitsToLocalUnitsHom w'
          (zetaUnitK p k L ζ hζ)) ^ (a (u w')).val := by
        rw [hφ eK w']
        rw [show eK (u w') = (Units.map
              ((algebraMap K (Place.localField K (u w'))).toMonoidHom) (zetaUnitK p k K ζ hζ))
              ^ (a (u w')).val from muIdeles_apply p k K ζ hζ a (u w')]
        rw [map_pow,
          NK.NUV2.LC.RouteB.localAlgebraMapUnits_algebraMap_units (L := K) (M := L)
            (hu w') (zetaUnitK p k K ζ hζ)]
        rw [zetaUnitK_map p k K L ζ hζ]
        rfl
      have hval : (a w).val = (a (u w')).val := congrArg ZMod.val (by rw [huw])
      rw [hval]
      exact key
    -- the morphism identity (A)
    have hz10 : Additive.toMul (z.hom (1 : ZMod p)) = zetaUnitK p k L ζ hζ :=
      Units.ext (hz.trans (zetaUnitK_coe p k L ζ hζ).symm)
    have hz1' : z.hom (1 : ZMod p) = Additive.ofMul (zetaUnitK p k L ζ hζ) := by
      rw [← hz10]
      exact (ofMul_toMul (z.hom (1 : ZMod p))).symm
    have hψ1 : ψ.hom (1 : ZMod p) = Additive.ofMul eL :=
      zmodToIdelesRep_apply_one p k L eL heL_tor hfix
    have hlocψ : ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL)
        = Additive.ofMul (eL w') := ideleToLocalUnits_apply w' eL
    have hlocz : ((unitsLocHom k ↥L w')).hom
          (Additive.ofMul (zetaUnitK p k L ζ hζ))
        = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w' (zetaUnitK p k L ζ hζ)) :=
      NK.HassePrinciple.unitsToLocalUnits_apply (K := k) (L := ↥L) w' (zetaUnitK p k L ζ hζ)
    have hA : (Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ ≫
        (ideleLocHom k ↥L w')
        = (a w).val • ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z ≫
            (unitsLocHom k ↥L w')) := by
      apply res_trivial_zmod_hom_ext (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype
      have e1 : (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ) ≫
            (ideleLocHom k ↥L w')).hom (1 : ZMod p)
          = ((ideleLocHom k ↥L w')).hom
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ)
                (1 : ZMod p)) := rfl
      have e2 : ((ideleLocHom k ↥L w')).hom
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ)
                (1 : ZMod p))
          = ((ideleLocHom k ↥L w')).hom (ψ.hom (1 : ZMod p)) := rfl
      have e3 : ((ideleLocHom k ↥L w')).hom (ψ.hom (1 : ZMod p))
          = ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL) :=
        congrArg (fun y => ((ideleLocHom k ↥L w')).hom y) hψ1
      have e4 : ((ideleLocHom k ↥L w')).hom (Additive.ofMul eL)
          = Additive.ofMul (eL w') := hlocψ
      have e5 : Additive.ofMul (eL w')
          = Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) ^ (a w).val) := congrArg (fun y => Additive.ofMul y) hcomp
      have e6 : Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) ^ (a w).val)
          = (a w).val • Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ)) :=
        ofMul_pow (a w).val (NK.HassePrinciple.unitsToLocalUnitsHom w' (zetaUnitK p k L ζ hζ))
      have e7 : (a w).val • Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w'
              (zetaUnitK p k L ζ hζ))
          = (a w).val • (((unitsLocHom k ↥L w')).hom
              (Additive.ofMul (zetaUnitK p k L ζ hζ))) :=
        congrArg (fun y => (a w).val • y) hlocz.symm
      have e8 : (a w).val • (((unitsLocHom k ↥L w')).hom
              (Additive.ofMul (zetaUnitK p k L ζ hζ)))
          = (a w).val • (((unitsLocHom k ↥L w')).hom (z.hom (1 : ZMod p))) :=
        (congrArg (fun y => (a w).val • ((unitsLocHom k ↥L w')).hom y)
          hz1').symm
      have e9 : (a w).val • (((unitsLocHom k ↥L w')).hom (z.hom (1 : ZMod p)))
          = (a w).val • (((unitsLocHom k ↥L w'))
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z)
                (1 : ZMod p))) := rfl
      have e10 : (a w).val • (((unitsLocHom k ↥L w'))
              (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) (1 : ZMod p)))
          = (a w).val • ((((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w')) (1 : ZMod p)) := rfl
      have e11 : (a w).val • ((((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w')) (1 : ZMod p))
          = ((a w).val • (((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z) ≫
              (unitsLocHom k ↥L w'))).hom (1 : ZMod p) := by
        rw [Rep.nsmul_hom, IntertwiningMap.nsmul_apply_aux]
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans
        (e9.trans (e10.trans e11)))))))))
    -- the `Ext` computation
    have hL' : (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (h.comp (Abelian.Ext.mk₀ ψ) (add_zero 2))).comp
        (Abelian.Ext.mk₀ ((ideleLocHom k ↥L w'))) (add_zero 2)
        = (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map ψ ≫
            (ideleLocHom k ↥L w'))) (add_zero 2) := by
      rw [extHRestrict_comp, Abelian.Ext.comp_assoc_of_third_deg_zero,
        Abelian.Ext.mk₀_comp_mk₀]
    have hR' : (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (h.comp (Abelian.Ext.mk₀ z) (add_zero 2))).comp
        (Abelian.Ext.mk₀ ((unitsLocHom k ↥L w'))) (add_zero 2)
        = (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype).map z ≫
            (unitsLocHom k ↥L w'))) (add_zero 2) := by
      rw [extHRestrict_comp, Abelian.Ext.comp_assoc_of_third_deg_zero,
        Abelian.Ext.mk₀_comp_mk₀]
    rw [hL', hR', Ext.comp_nsmul, ← mk₀_nsmul_aux, ← hA]
  · -- the pairing identity
    have hc0' : (muClassHom p k K ζ hζ a ha).hom (1 : ZMod p) = muClass p k K ζ hζ a :=
      muClassHom_apply_one p k K ζ hζ a ha
    have hcl : (classIncl k K L).hom (muClass p k K ζ hζ a)
        = Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a))) := by
      show (classIncl k K L).hom
          (Additive.ofMul (IdeleClassGroup.mk K (muIdeles p k K ζ hζ a))) = _
      exact hι (muIdeles p k K ζ hζ a)
    have hLHS : (trivRes (galRes k K L) (ZMod p) ≫
        (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫ classIncl k K L).hom
          (1 : ZMod p) = Additive.ofMul (IdeleClassGroup.mk L eL) := by
      have e1 : (trivRes (galRes k K L) (ZMod p) ≫
            (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫
            classIncl k K L).hom (1 : ZMod p)
          = (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom
                ((trivRes (galRes k K L) (ZMod p)).hom (1 : ZMod p))) := rfl
      have e2 : (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom ((trivRes (galRes k K L) (ZMod p)).hom (1 : ZMod p)))
          = (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom (1 : ZMod p)) := by
        rw [trivRes_hom_one]
      have e3 : (classIncl k K L).hom (((Rep.resFunctor (galRes k K L)).map
              (muClassHom p k K ζ hζ a ha)).hom (1 : ZMod p))
          = (classIncl k K L).hom ((muClassHom p k K ζ hζ a ha).hom (1 : ZMod p)) := rfl
      have e4 : (classIncl k K L).hom ((muClassHom p k K ζ hζ a ha).hom (1 : ZMod p))
          = (classIncl k K L).hom (muClass p k K ζ hζ a) :=
        congrArg (fun y => (classIncl k K L).hom y) hc0'
      have e5 : (classIncl k K L).hom (muClass p k K ζ hζ a)
          = Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a))) := hcl
      have e6 : Additive.ofMul (IdeleClassGroup.mk L (φ (muIdeles p k K ζ hζ a)))
          = Additive.ofMul (IdeleClassGroup.mk L eL) := rfl
      exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
    have hRHS : (ψ ≫ NK.HassePrinciple.classGroupMap k L).hom (1 : ZMod p)
        = Additive.ofMul (IdeleClassGroup.mk L eL) := by
      have hψ1 : ψ.hom (1 : ZMod p) = Additive.ofMul eL :=
        zmodToIdelesRep_apply_one p k L eL heL_tor hfix
      have e1 : (ψ ≫ NK.HassePrinciple.classGroupMap k L).hom (1 : ZMod p)
          = (NK.HassePrinciple.classGroupMap k L).hom (ψ.hom (1 : ZMod p)) := rfl
      have e2 : (NK.HassePrinciple.classGroupMap k L).hom (ψ.hom (1 : ZMod p))
          = (NK.HassePrinciple.classGroupMap k L).hom (Additive.ofMul eL) :=
        congrArg (fun y => (NK.HassePrinciple.classGroupMap k L).hom y) hψ1
      have e3 : (NK.HassePrinciple.classGroupMap k L).hom (Additive.ofMul eL)
          = Additive.ofMul (IdeleClassGroup.mk L eL) :=
        NK.HassePrinciple.classGroupMap_apply k L eL
      exact e1.trans (e2.trans e3)
    have hB : trivRes (galRes k K L) (ZMod p) ≫
        (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫ classIncl k K L
        = ψ ≫ NK.HassePrinciple.classGroupMap k L :=
      zmod_trivial_hom_ext _ _ (hLHS.trans hRHS.symm)
    have hphi : phiTriv (k := k) (K := K) (L := L) (ZMod p)
        (Abelian.Ext.mk₀ (muClassHom p k K ζ hζ a ha)) h
        = h.comp (Abelian.Ext.mk₀ (trivRes (galRes k K L) (ZMod p) ≫
            (Rep.resFunctor (galRes k K L)).map (muClassHom p k K ζ hζ a ha) ≫
            classIncl k K L)) (add_zero 2) :=
      phiTriv_mk0_eq (k := k) (K := K) (L := L) (ZMod p) (muClassHom p k K ζ hζ a ha) h
    rw [hphi, hB, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

end Work.SSGRoute
