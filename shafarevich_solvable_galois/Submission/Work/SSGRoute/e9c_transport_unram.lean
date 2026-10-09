import Mathlib
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.ext_corestriction
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
import Submission.NK.GlobalCFT.Inclusion.globalCFT_fixed_idele_mem_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Auxiliary computations for `e9c_transport_unram` -/

variable {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]

/-- The integral local units `𝒪_wˣ` as a `Coeff`-representation, with the coefficient universe
pinned (the bare `NK.HassePrinciple.localUnitsSubRep` leaves it free). -/
noncomputable abbrev localUnitsSubP (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    Rep.{0, 0, 0} Coeff (decompK (k := k) w) := NK.HassePrinciple.localUnitsSubRep k K w

/-- The inclusion `𝒪_wˣ ↪ K_wˣ`, universe-pinned. -/
noncomputable abbrev localUnitsInclP (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    localUnitsSubP k K w ⟶ localUnitsK (k := k) (K := K) w :=
  NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w

/-- Computation rule: `ideleToLocalUnits` is evaluation of the `w`-component. -/
theorem ideleToLocalUnits_ofMul_eq (K' : Type) [Field K'] [NumberField K'] [Algebra k K']
    [FiniteDimensional k K'] [IsGalois k K'] (w : Place K') (y : Idele K') :
    (NK.HassePrinciple.ideleToLocalUnits k K' w).hom (Additive.ofMul y) =
      Additive.ofMul (y w) := rfl

/-- **The `w`-component of the level map is the local algebra map on the `u`-component.** -/
theorem resMap_idleRepMap_comp_ideleToLocalUnits (u : Place K) (w : Place L)
    (hw : Place.LiesOver w u)
    (ι : Rep.res (decompKRestrict k K L u w hw) (localUnitsK (k := k) (K := K) u) ⟶
      localUnitsK (k := k) (K := L) w)
    (hι : ∀ y : (Place.localField K u)ˣ, ι.hom (Additive.ofMul y)
      = Additive.ofMul (Place.localAlgebraMapUnits w u hw y)) :
    Rep.resMap (decompK (k := k) w).subtype (idleRepMap k K L) ≫
        NK.HassePrinciple.ideleToLocalUnits k L w
      = Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι := by
  apply Rep.hom_ext
  ext x
  obtain ⟨a, ha⟩ : ∃ a : Idele K, x = Additive.ofMul a := ⟨Additive.toMul x, rfl⟩
  rw [ha]
  show Additive.ofMul (((canonicalIdleData k K L).φ a) w) = ι.hom (Additive.ofMul (a u))
  rw [(canonicalIdleData k K L).hφ a w, hι]
  have hpl : (canonicalIdleData k K L).u w = u :=
    place_liesOver_unique w ((canonicalIdleData k K L).hu w) hw
  rw [NK.HassePrinciple.localAlgebraMapUnits_cast w hpl ((canonicalIdleData k K L).hu w) hw,
    ← NK.GlobalCFT.Inclusion.globalCFT_ideles_component_transport a hpl]

/-- **The local units map carries the integral units into the integral units.** -/
theorem exists_factor_localUnitsIncl (u : Place K) (w : Place L) (hw : Place.LiesOver w u)
    (f : decompK (k := k) w →* decompK (k := k) u)
    (ι : Rep.res f (localUnitsK (k := k) (K := K) u) ⟶ localUnitsK (k := k) (K := L) w)
    (hι : ∀ y : (Place.localField K u)ˣ, ι.hom (Additive.ofMul y)
      = Additive.ofMul (Place.localAlgebraMapUnits w u hw y)) :
    ∃ ι' : Rep.res f (localUnitsSubP k K u) ⟶
        localUnitsSubP k L w,
      Rep.resMap f (localUnitsInclP k K u) ≫ ι
        = ι' ≫ localUnitsInclP k L w := by
  classical
  have hψ' : ∀ y : ↥(Place.localUnits K u),
      (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom
          (Additive.ofMul y)
        = Additive.ofMul (Place.localAlgebraMapUnits w u hw y.1) := by
    intro y
    rw [Rep.comp_apply, Rep.resMap_hom_apply]
    exact hι (↑y : (Place.localField K u)ˣ)
  let gfun : Additive ↥(Place.localUnits K u) → Additive ↥(Place.localUnits L w) := fun a =>
    Additive.ofMul ⟨Place.localAlgebraMapUnits w u hw (Additive.toMul a).1,
      NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits hw (Additive.toMul a).2⟩
  have hgf : ∀ a : Additive ↥(Place.localUnits K u),
      (localUnitsInclP k L w).hom (gfun a)
        = (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom a := by
    intro a
    have h1 : (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom a
        = Additive.ofMul (Place.localAlgebraMapUnits w u hw (Additive.toMul a).1) := by
      rw [show a = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm]
      exact hψ' (Additive.toMul a)
    calc (localUnitsInclP k L w).hom (gfun a)
        = Additive.ofMul (Place.localAlgebraMapUnits w u hw (Additive.toMul a).1) := rfl
      _ = (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom a :=
          h1.symm
  have hinj : ∀ {a b : Additive ↥(Place.localUnits L w)},
      (localUnitsInclP k L w).hom a
        = (localUnitsInclP k L w).hom b → a = b := by
    intro a b h
    apply Additive.toMul.injective
    exact Subtype.ext (Additive.toMul.injective h)
  have hadd : ∀ a b : Additive ↥(Place.localUnits K u), gfun (a + b) = gfun a + gfun b := by
    intro a b
    refine hinj ?_
    calc (localUnitsInclP k L w).hom (gfun (a + b))
        = (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom (a + b) :=
          hgf (a + b)
      _ = (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom a
            + (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom b :=
          map_add _ a b
      _ = (localUnitsInclP k L w).hom (gfun a)
            + (localUnitsInclP k L w).hom (gfun b) := by
          rw [hgf a, hgf b]
      _ = (localUnitsInclP k L w).hom (gfun a + gfun b) :=
          (map_add _ _ _).symm
  have hsmul : ∀ (n : Coeff) (a : Additive ↥(Place.localUnits K u)), gfun (n • a) = n • gfun a := by
    intro n a
    refine hinj ?_
    calc (localUnitsInclP k L w).hom (gfun (n • a))
        = (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom (n • a) :=
          hgf (n • a)
      _ = n • (Rep.resMap f (localUnitsInclP k K u) ≫ ι).hom a :=
          map_smul _ n a
      _ = n • (localUnitsInclP k L w).hom (gfun a) := by
          rw [hgf a]
      _ = (localUnitsInclP k L w).hom (n • gfun a) :=
          (map_smul _ n _).symm
  have hintw : ∀ (σ : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w))
      (a : Additive ↥(Place.localUnits K u)),
      gfun (((Rep.res f (localUnitsSubP k K u)).ρ σ) a)
        = ((localUnitsSubP k L w).ρ σ) (gfun a) := by
    intro σ a
    refine hinj ?_
    calc (localUnitsInclP k L w).hom
            (gfun (((Rep.res f (localUnitsSubP k K u)).ρ σ) a))
        = (Rep.resMap f (localUnitsInclP k K u) ≫ ι)
            (((Rep.res f (localUnitsSubP k K u)).ρ σ) a) :=
          hgf (((Rep.res f (localUnitsSubP k K u)).ρ σ) a)
      _ = (localUnitsK (k := k) (K := L) w).ρ σ
            ((Rep.resMap f (localUnitsInclP k K u) ≫ ι) a) :=
          Rep.hom_comm_apply
            (Rep.resMap f (localUnitsInclP k K u) ≫ ι) σ a
      _ = (localUnitsK (k := k) (K := L) w).ρ σ
            ((localUnitsInclP k L w).hom (gfun a)) := by
          rw [hgf a]
      _ = (localUnitsInclP k L w).hom
            (((localUnitsSubP k L w).ρ σ) (gfun a)) :=
          (Rep.hom_comm_apply (localUnitsInclP k L w) σ
            (gfun a)).symm
  let ι' : Rep.res f (localUnitsSubP k K u) ⟶
      localUnitsSubP k L w :=
    Rep.ofHom
      { toFun := gfun
        map_add' := hadd
        map_smul' := hsmul
        isIntertwining' := fun σ => LinearMap.ext (hintw σ) }
  have hι'_hom : ∀ a : ↑(Rep.res f (localUnitsSubP k K u)),
      (Rep.Hom.hom ι') a = gfun a := fun a => rfl
  refine ⟨ι', ?_⟩
  apply Rep.hom_ext
  ext a
  change (Rep.Hom.hom (Rep.resMap f (localUnitsInclP k K u) ≫ ι)) a
      = (Rep.Hom.hom (ι' ≫ localUnitsInclP k L w)) a
  conv_rhs => rw [Rep.comp_apply]
  rw [hι'_hom a]
  exact (hgf a).symm

/-- **E9c, transport of *unramifiedness* of a local component along the level map `K → L`.**

Same setting as `e9c_transport_zero` (`Submission/Work/SSGRoute/E9c/Core.lean`): if the
`u`-component of `z ∈ Ext^r(M, 𝕀_K)` is unramified (comes from `𝒪_uˣ` via
`NK.HassePrinciple.localUnitsIncl`), then the `w`-component of the pushed class
`extRes (galRes k K L) z ≫ φ` is unramified. -/
theorem e9c_transport_unram {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext M (Work.SSGRoute.idelesRepP k K) r) (u : Place K) (w : Place L)
    (hw : Place.LiesOver w u)
    (hz : IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u z)) :
    IsUnramifiedExt (k := k) (K := L) w
      (extLoc (k := k) (K := L) w
        ((extRes (galRes k K L) z).comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero r))) := by
  classical
  obtain ⟨ι, hι⟩ :=
    localUnitsMap_exists k K L u w hw (decompKRestrict k K L u w hw) (fun σ => rfl)
  obtain ⟨ι', hι'⟩ :=
    exists_factor_localUnitsIncl (k := k) (K := K) (L := L) u w hw
      (decompKRestrict k K L u w hw) ι hι
  rw [IsUnramifiedExt] at hz
  obtain ⟨ζ', hζ'⟩ := hz
  refine ⟨(extRes (decompKRestrict k K L u w hw) ζ').comp (Abelian.Ext.mk₀ ι')
    (add_zero r), ?_⟩
  -- (1) unfold `extLoc` and push `extRes` through `comp` / `mk₀`
  have h1 : extLoc (k := k) (K := L) w ((extRes (galRes k K L) z).comp
        (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero r))
      = (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype (idleRepMap k K L) ≫
            NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero r) := by
    rw [extLoc, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
    try rfl
  -- (2) the coefficient identity
  have h2 : (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype (idleRepMap k K L) ≫
          NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero r)
      = (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι)) (add_zero r) := by
    rw [resMap_idleRepMap_comp_ideleToLocalUnits (k := k) (K := K) (L := L) u w hw ι hι]
  -- (3) split the composite coefficient map
  have h3 : (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι)) (add_zero r)
      = ((extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (NK.HassePrinciple.ideleToLocalUnits k K u))) (add_zero r)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by
    rw [← Abelian.Ext.mk₀_comp_mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u)) ι]
    exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero r)).symm
  -- (4) the two ways of restricting `z` to the decomposition group of `w` agree
  have h4 : extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)
      = extRes (decompKRestrict k K L u w hw) (extRes (decompK (k := k) u).subtype z) := by
    have hA : extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)
        = z.mapExactFunctor (Rep.resFunctor (galRes k K L) ⋙
            Rep.resFunctor (decompK (k := k) w).subtype) :=
      ext_mapExactFunctor_comp_functor_aux (C := Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
        (D := Rep.{0, 0, 0} Coeff (L ≃ₐ[k] L)) (E := Rep.{0, 0, 0} Coeff (decompK (k := k) w))
        (Rep.resFunctor (galRes k K L)) (Rep.resFunctor (decompK (k := k) w).subtype) r M
        (idelesRepP k K) z
    have hB : extRes (decompKRestrict k K L u w hw) (extRes (decompK (k := k) u).subtype z)
        = z.mapExactFunctor (Rep.resFunctor (decompK (k := k) u).subtype ⋙
            Rep.resFunctor (decompKRestrict k K L u w hw)) :=
      ext_mapExactFunctor_comp_functor_aux (C := Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
        (D := Rep.{0, 0, 0} Coeff (decompK (k := k) u))
        (E := Rep.{0, 0, 0} Coeff (decompK (k := k) w))
        (Rep.resFunctor (decompK (k := k) u).subtype)
        (Rep.resFunctor (decompKRestrict k K L u w hw)) r M (idelesRepP k K) z
    rw [hA, hB]
    rfl
  -- (5) pushing the localised class at `u` through `extRes`
  have h5 : (extRes (decompKRestrict k K L u w hw) (extRes (decompK (k := k) u).subtype z)).comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u))) (add_zero r)
      = extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z) := by
    rw [show extLoc (k := k) (K := K) u z
        = (extRes (decompK (k := k) u).subtype z).comp
            (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K u)) (add_zero r) from rfl]
    conv_rhs => rw [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    try rfl
  -- (6) the unramifiedness of `z` at `u`
  have h6 : extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z)
      = (extRes (decompKRestrict k K L u w hw) ζ').comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (localUnitsInclP k K u))) (add_zero r) := by
    conv_lhs => rw [hζ', extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    try rfl
  -- (7) the integral-units factorisation
  have h7 : ((extRes (decompKRestrict k K L u w hw) ζ').comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
          (localUnitsInclP k K u))) (add_zero r)).comp
        (Abelian.Ext.mk₀ ι) (add_zero r)
      = ((extRes (decompKRestrict k K L u w hw) ζ').comp (Abelian.Ext.mk₀ ι')
          (add_zero r)).comp
          (Abelian.Ext.mk₀ (localUnitsInclP k L w))
          (add_zero r) := by
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero r),
      Abelian.Ext.mk₀_comp_mk₀, hι',
      ← Abelian.Ext.mk₀_comp_mk₀ ι' (localUnitsInclP k L w),
      ← Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero r)]
    try rfl
  calc
    extLoc (k := k) (K := L) w ((extRes (galRes k K L) z).comp
        (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero r))
      = (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype (idleRepMap k K L) ≫
            NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero r) := h1
    _ = (extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι)) (add_zero r) := h2
    _ = ((extRes (decompK (k := k) w).subtype (extRes (galRes k K L) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (NK.HassePrinciple.ideleToLocalUnits k K u))) (add_zero r)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := h3
    _ = ((extRes (decompKRestrict k K L u w hw)
            (extRes (decompK (k := k) u).subtype z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (NK.HassePrinciple.ideleToLocalUnits k K u))) (add_zero r)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by rw [h4]
    _ = (extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by rw [h5]
    _ = ((extRes (decompKRestrict k K L u w hw) ζ').comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K L u w hw)
            (localUnitsInclP k K u))) (add_zero r)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by rw [h6]
    _ = ((extRes (decompKRestrict k K L u w hw) ζ').comp (Abelian.Ext.mk₀ ι')
          (add_zero r)).comp
          (Abelian.Ext.mk₀ (localUnitsInclP k L w))
          (add_zero r) := h7

end Work.SSGRoute
