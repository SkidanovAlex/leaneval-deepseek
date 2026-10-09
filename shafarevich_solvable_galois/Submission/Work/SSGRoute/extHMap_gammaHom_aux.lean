import Mathlib
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.augSES_shortExact
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary material for `extHMap_gammaHom_eq`

The group-naturality of the degree-one bridge `H¹(G,M) ≅ Ext¹_G(ℤ,M)` is proved by producing a
morphism of short complexes `Φ : augSES H ⟶ (augSES G).map (Rep.resFunctor r)` induced by the
algebra map `k[H] → k[G]`, `γ ↦ r γ`.  This file contains the geometric part of the construction:
the algebra map `theta`, its restriction `thetaI` to the augmentation ideals, the morphism `Phi`
of short complexes, and the cocycle compatibility `thetaI_cocycle`.
-/

open CategoryTheory SSGRoute.PTExt

set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.ExtHMapAux

variable {G H : Type} [Group G] [Group H] (r : H →* G)

/-! ## The regular representation is multiplication -/

/-- The left regular action of `G` on `k[G]` is left multiplication. -/
theorem regRep_ρ_apply (g : G) (y : Work.SSGRoute.ExtH1.regRep G) :
    (Work.SSGRoute.ExtH1.regRep G).ρ g y = Work.SSGRoute.ExtH1.ebas G g * y := by
  rw [show (Work.SSGRoute.ExtH1.regRep G).ρ g =
      (Representation.ofMulAction Coeff G G).asAlgebraHom (MonoidAlgebra.single g 1) from
    (Representation.asAlgebraHom_single_one (Representation.ofMulAction Coeff G G) g).symm]
  exact Representation.asAlgebraHom_ofMulAction_smul_eq_mul (MonoidAlgebra.single g 1) y

/-! ## The algebra map `k[H] → k[G]`, `γ ↦ r γ` -/

/-- The algebra map `k[H] → k[G]` sends a basis element `γ` to `r γ`. -/
theorem theta_ebas (x : H) :
    (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) (Work.SSGRoute.ExtH1.ebas H x)
      = Work.SSGRoute.ExtH1.ebas G (r x) := by
  simp only [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    Work.SSGRoute.ExtH1.ebas]

/-- Coefficients of the image under `mapDomainAlgHom`. -/
theorem coeff_mapDomainAlgHom (x : MonoidAlgebra Coeff H) :
    MonoidAlgebra.coeff ((MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) x)
      = Finsupp.mapDomain (⇑r) (MonoidAlgebra.coeff x) := by
  rw [show (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) x
      = MonoidAlgebra.mapDomain (⇑r) x from rfl,
    MonoidAlgebra.mapDomain, MonoidAlgebra.coeff_ofCoeff]

/-- The algebra map `γ ↦ r γ` commutes with the augmentation. -/
theorem theta_augHom (x : MonoidAlgebra Coeff H) :
    (Work.SSGRoute.ExtH1.augHom G).hom ((MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) x)
      = (Work.SSGRoute.ExtH1.augHom H).hom x := by
  rw [Work.SSGRoute.ExtH1.augHom_eq_sum_coeff, Work.SSGRoute.ExtH1.augHom_eq_sum_coeff,
    coeff_mapDomainAlgHom]
  rw [Finsupp.sum_mapDomain_index (by intro b; rfl) (by intro b m1 m2; rfl)]

/-- The algebra map `k[H] → k[G]`, as a morphism of representations
`regRep H ⟶ Rep.res r (regRep G)`. -/
noncomputable def theta : Work.SSGRoute.ExtH1.regRep H ⟶ Rep.res r (Work.SSGRoute.ExtH1.regRep G) :=
  Rep.ofHom
    { toLinearMap := (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r).toLinearMap
      isIntertwining' := fun h => by
        apply LinearMap.ext
        intro x
        show (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) ((Work.SSGRoute.ExtH1.regRep H).ρ h x)
          = (Work.SSGRoute.ExtH1.regRep G).ρ (r h) ((MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) x)
        rw [regRep_ρ_apply (G := H) h, regRep_ρ_apply (G := G) (r h),
          map_mul (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r), theta_ebas (G := G) r h] }

/-- `theta` is the algebra map. -/
theorem theta_apply' (x : MonoidAlgebra Coeff H) :
    (theta r).hom x = (MonoidAlgebra.mapDomainAlgHom Coeff Coeff r) x := rfl

/-! ## The restriction to the augmentation ideals -/

/-- The restriction of `theta` to the augmentation ideals, as a linear map. -/
noncomputable def thetaILin :
    ↥(Work.SSGRoute.ExtH1.augSub H) →ₗ[Coeff] ↥(Work.SSGRoute.ExtH1.augSub G) :=
  LinearMap.codRestrict (Work.SSGRoute.ExtH1.augSub G)
    ((theta r).hom.toLinearMap.comp (Submodule.subtype (Work.SSGRoute.ExtH1.augSub H)))
    (fun x => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply]
      change (Work.SSGRoute.ExtH1.augHom G).hom ((theta r).hom (x : MonoidAlgebra Coeff H)) = 0
      rw [theta_apply', theta_augHom]
      exact x.2)

/-- The underlying element of `thetaILin`. -/
theorem thetaILin_coe (x : ↥(Work.SSGRoute.ExtH1.augSub H)) :
    ((thetaILin r x : ↥(Work.SSGRoute.ExtH1.augSub G)) : MonoidAlgebra Coeff G)
      = (theta r).hom (x : MonoidAlgebra Coeff H) := rfl

/-- `thetaILin` is compatible with the actions. -/
theorem thetaILin_intertwining (h : H) (x : ↥(Work.SSGRoute.ExtH1.augSub H)) :
    thetaILin r ((Work.SSGRoute.ExtH1.augI H).ρ h x)
      = (Work.SSGRoute.ExtH1.augI G).ρ (r h) (thetaILin r x) := by
  apply Subtype.ext
  show (theta r).hom
        (((Work.SSGRoute.ExtH1.augI H).ρ h x : ↥(Work.SSGRoute.ExtH1.augSub H)) :
          MonoidAlgebra Coeff H)
      = (Work.SSGRoute.ExtH1.regRep G).ρ (r h)
        ((thetaILin r x : ↥(Work.SSGRoute.ExtH1.augSub G)) : MonoidAlgebra Coeff G)
  rw [show (((Work.SSGRoute.ExtH1.augI H).ρ h x : ↥(Work.SSGRoute.ExtH1.augSub H)) :
        MonoidAlgebra Coeff H)
      = (Work.SSGRoute.ExtH1.regRep H).ρ h (x : MonoidAlgebra Coeff H) from rfl]
  rw [thetaILin_coe]
  exact Rep.hom_comm_apply (theta r) h (x : MonoidAlgebra Coeff H)

/-- The restriction of `theta` to the augmentation ideals, as a morphism of representations. -/
noncomputable def thetaI : Work.SSGRoute.ExtH1.augI H ⟶ Rep.res r (Work.SSGRoute.ExtH1.augI G) :=
  Rep.ofHom
    { toLinearMap := thetaILin r
      isIntertwining' := fun h => by
        apply LinearMap.ext
        intro x
        exact thetaILin_intertwining r h x }

/-- `thetaI` on the generators `γ - 1`. -/
theorem thetaILin_augDiff (γ : H) :
    thetaILin r (Work.SSGRoute.ExtH1.augDiff H γ)
      = Work.SSGRoute.ExtH1.augDiff G (r γ) := by
  apply Subtype.ext
  rw [thetaILin_coe]
  show (theta r).hom ((Work.SSGRoute.ExtH1.ebas H γ - Work.SSGRoute.ExtH1.ebas H 1))
      = Work.SSGRoute.ExtH1.ebas G (r γ) - Work.SSGRoute.ExtH1.ebas G 1
  rw [map_sub, theta_apply', theta_apply', theta_ebas, theta_ebas, map_one]

/-- `thetaI` on the generators `γ - 1`. -/
theorem thetaI_augDiff (γ : H) :
    (thetaI r).hom (Work.SSGRoute.ExtH1.augDiff H γ)
      = Work.SSGRoute.ExtH1.augDiff G (r γ) :=
  thetaILin_augDiff r γ

/-! ## The morphism of short complexes `augSES H ⟶ (augSES G).map (Rep.resFunctor r)` -/

/-- First square of the morphism of short complexes. -/
theorem comm12 : thetaI r ≫ Rep.resMap r (Work.SSGRoute.ExtH1.augIncl G)
    = Work.SSGRoute.ExtH1.augIncl H ≫ theta r := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (Rep.resMap r (Work.SSGRoute.ExtH1.augIncl G)).hom ((thetaI r).hom x)
    = (theta r).hom ((Work.SSGRoute.ExtH1.augIncl H).hom x)
  rw [Rep.resMap_hom_apply]
  rfl

/-- Second square of the morphism of short complexes. -/
theorem comm23 : theta r ≫ Rep.resMap r (Work.SSGRoute.ExtH1.augHom G)
    = Work.SSGRoute.ExtH1.augHom H ≫ unitRes r := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (Rep.resMap r (Work.SSGRoute.ExtH1.augHom G)).hom ((theta r).hom x)
    = (unitRes r).hom ((Work.SSGRoute.ExtH1.augHom H).hom x)
  rw [Rep.resMap_hom_apply]
  show (Work.SSGRoute.ExtH1.augHom G).hom ((theta r).hom x)
    = (Work.SSGRoute.ExtH1.augHom H).hom x
  rw [theta_apply', theta_augHom]

/-- The induced morphism of short complexes. -/
noncomputable def Phi : Work.SSGRoute.ExtH1.augSES H ⟶
    (Work.SSGRoute.ExtH1.augSES G).map (Rep.resFunctor r) :=
  { τ₁ := thetaI r, τ₂ := theta r, τ₃ := unitRes r, comm₁₂ := comm12 r, comm₂₃ := comm23 r }

/-! ## The cocycle compatibility -/

/-- Extensionality for morphisms `augI H ⟶ Rep.res r (modRep G M)` on the elements `γ - 1`. -/
theorem hom_ext_augDiff_res {M : Type} [AddCommGroup M] [Module Coeff M] [DistribMulAction G M]
    (f g : Work.SSGRoute.ExtH1.augI H ⟶ Rep.res r (SSGRoute.PTExt.modRep G M))
    (h : ∀ γ : H, f.hom (Work.SSGRoute.ExtH1.augDiff H γ)
      = g.hom (Work.SSGRoute.ExtH1.augDiff H γ)) : f = g := by
  apply Rep.hom_ext (A := Work.SSGRoute.ExtH1.augI H)
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (Rep.Hom.hom f).toLinearMap x = (Rep.Hom.hom g).toLinearMap x
  rw [← Work.SSGRoute.ExtH1.sum_coeff_smul_augDiff H x, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [map_smul, map_smul, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply, h γ]

/-- **The cocycle identity**: for a `1`-cocycle `φ : G → M`, the morphism `thetaI` intertwines
the derivation `cocycleHom_G φ` with the pulled back derivation `cocycleHom_H (φ ∘ r)`. -/
theorem thetaI_cocycle {M : Type} [AddCommGroup M] [Module Coeff M] [DistribMulAction G M]
    (φ : G → M) (hφ : Work.SSGRoute.ExtH1.IsCrossedHom (G := G) (M := M) φ) :
    letI : DistribMulAction H M := DistribMulAction.compHom M r
    ∀ (hφr : Work.SSGRoute.ExtH1.IsCrossedHom (G := H) (M := M) (fun h => φ (r h))),
      thetaI r ≫ Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ)
        = Work.SSGRoute.ExtH1.cocycleHom (G := H) (M := M) (fun h => φ (r h)) hφr := by
  intro hφr
  letI : DistribMulAction H M := DistribMulAction.compHom M r
  refine hom_ext_augDiff_res r
    (f := thetaI r ≫ Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ))
    (g := Work.SSGRoute.ExtH1.cocycleHom (G := H) (M := M) (fun h => φ (r h)) hφr) ?_
  intro γ
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, Rep.resMap_hom_apply]
  rw [show (thetaI r).hom (Work.SSGRoute.ExtH1.augDiff H γ)
      = Work.SSGRoute.ExtH1.augDiff G (r γ) from thetaI_augDiff r γ]
  rw [Work.SSGRoute.ExtH1.cocycleHom_augDiff (G := G) (M := M) φ hφ (r γ)]
  exact (Work.SSGRoute.ExtH1.cocycleHom_augDiff (G := H) (M := M) (fun h => φ (r h)) hφr γ).symm

/-! ## The `Ext`-level naturality -/

/-- The identity of the trivial module is `unitRes`. -/
theorem unitRes_eq_id : SSGRoute.PTExt.unitRes r = 𝟙 (SSGRoute.PTExt.unitRep H) :=
  Rep.hom_ext rfl

/-- `extHMap` along the identity coefficient morphism is `extRes`. -/
theorem extHMap_one_eq_extRes {A : Rep.{0} Coeff G} {n : ℕ} (y : extH A n) :
    SSGRoute.PTExt.extHMap r (𝟙 (Rep.res r A)) y = SSGRoute.PTExt.extRes r y := by
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes]
  rw [Abelian.Ext.comp_mk₀_id, unitRes_eq_id r]
  exact Abelian.Ext.mk₀_id_comp (y.mapExactFunctor (Rep.resFunctor r))

/-- Pre-composition with `mk₀ (unitRes r)` is the identity. -/
theorem mk₀_unitRes_comp {Y : Rep.{0} Coeff H} {n : ℕ}
    (X : Abelian.Ext (Rep.res r (SSGRoute.PTExt.unitRep G)) Y n) :
    (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes r)).comp X (zero_add n) = X := by
  rw [unitRes_eq_id r]
  exact Abelian.Ext.mk₀_id_comp X

/-- **The `Ext`-level naturality of the degree-one bridge** along `r : H →* G`: both sides are the
`Ext¹`-class of the pulled-back cocycle. -/
theorem extHMap_extClass_cocycle {M : Type} [AddCommGroup M] [Module Coeff M]
    [DistribMulAction G M] (φ : G → M)
    (hφ : Work.SSGRoute.ExtH1.IsCrossedHom (G := G) (M := M) φ) :
    letI : DistribMulAction H M := DistribMulAction.compHom M r
    ∀ (hφr : Work.SSGRoute.ExtH1.IsCrossedHom (G := H) (M := M) (fun h => φ (r h))),
      SSGRoute.PTExt.extHMap r (𝟙 (Rep.res r (SSGRoute.PTExt.modRep G M)))
        ((Work.SSGRoute.augSES_shortExact G).extClass.comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ))
          (add_zero 1))
      = (Work.SSGRoute.augSES_shortExact H).extClass.comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.ExtH1.cocycleHom (G := H) (M := M) (fun h => φ (r h))
            hφr)) (add_zero 1) := by
  intro hφr
  letI : DistribMulAction H M := DistribMulAction.compHom M r
  have h2 : ((Work.SSGRoute.ExtH1.augSES G).map (Rep.resFunctor r)).ShortExact :=
    ShortComplex.ShortExact.map_of_exact (Work.SSGRoute.augSES_shortExact G) (Rep.resFunctor r)
  have hext : h2.extClass
      = (Work.SSGRoute.augSES_shortExact G).extClass.mapExactFunctor (Rep.resFunctor r) :=
    (Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor r)
      (Work.SSGRoute.augSES_shortExact G)).symm
  have hnat : (Work.SSGRoute.augSES_shortExact H).extClass.comp
        (Abelian.Ext.mk₀ (thetaI r)) (add_zero 1)
      = (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes r)).comp h2.extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality (Work.SSGRoute.augSES_shortExact H) h2 (Phi r)
  have hcoc := thetaI_cocycle (H := H) (G := G) r φ hφ hφr
  have hRHS : (Work.SSGRoute.augSES_shortExact H).extClass.comp
        (Abelian.Ext.mk₀ (Work.SSGRoute.ExtH1.cocycleHom (G := H) (M := M) (fun h => φ (r h))
          hφr)) (add_zero 1)
      = (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes r)).comp
          (h2.extClass.comp
            (Abelian.Ext.mk₀ (Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ)))
            (add_zero 1)) (zero_add 1) := by
    rw [← hcoc, ← Abelian.Ext.mk₀_comp_mk₀]
    rw [← Abelian.Ext.comp_assoc (Work.SSGRoute.augSES_shortExact H).extClass
      (Abelian.Ext.mk₀ (thetaI r))
      (Abelian.Ext.mk₀ (Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ)))
      (add_zero 1) (zero_add 0) (by omega)]
    rw [hnat]
    rw [Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes r)) h2.extClass
      (Abelian.Ext.mk₀ (Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ)))
      (zero_add 1) (add_zero 1) (by omega)]
  rw [hRHS, mk₀_unitRes_comp]
  rw [extHMap_one_eq_extRes r, SSGRoute.PTExt.extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]
  rw [show (Rep.resFunctor r).map (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ)
      = Rep.resMap r (Work.SSGRoute.ExtH1.cocycleHom (G := G) (M := M) φ hφ) from rfl]
  rw [← hext]

end Work.SSGRoute.ExtHMapAux
