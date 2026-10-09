import Mathlib
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E9c.Unram
import Submission.Work.SSGRoute.e9c_transport_zero
import Submission.Work.SSGRoute.e9c_unram_pairing
import Submission.Work.SSGRoute.extIdele_localisation_injective
import Submission.Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-- `𝒪_wˣ` with the carrier universe pinned to `0` (`Coeff = ULift ℤ`). -/
private noncomputable abbrev localUnitsSubP (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    Rep.{0} Coeff (decompK (k := k) w) := NK.HassePrinciple.localUnitsSubRep k K w

/-- The inclusion `𝒪_wˣ ↪ K_wˣ` with the carrier universe pinned to `0`. -/
private noncomputable abbrev localUnitsInclP (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    localUnitsSubP k K w ⟶ localUnitsK (k := k) (K := K) w :=
  NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w

/-- The Yoneda pairing of the zero class is zero. -/
private theorem yonedaPair_zero {G : Type} [Group G] {M A : Rep.{0, 0, 0} Coeff G} {s r : ℕ}
    (h : extH M s) : yonedaPair (0 : Abelian.Ext M A r) h = 0 := by
  simp [yonedaPair]

/-! ## The local step: the local units map preserves unramifiedness

`Core`-compatible version of `Work.SSGRoute.E9c.factorLocalUnitsIncl` /
`Work.SSGRoute.E9c.isUnramifiedExt_extHMap_localUnits`. -/

/-- **The local units map restricted to the integral units.**  For places `w' | w` of `L | K`
and the local embedding of unit groups `K_wˣ → L_{w'}ˣ`, the map sends `𝒪_wˣ` into `𝒪_{w'}ˣ`,
hence factors through the inclusion of the integral units:
`resMap f (𝒪_wˣ ↪ K_wˣ) ≫ (K_wˣ → L_{w'}ˣ) = ι' ≫ (𝒪_{w'}ˣ ↪ L_{w'}ˣ)`. -/
private theorem factorLocalUnitsIncl {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] (w : Place K) (w' : Place L) (hw : Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (K ≃ₐ[k] K) w)
    (ι : Rep.res f (localUnitsK (k := k) (K := K) w) ⟶ localUnitsK (k := k) (K := L) w')
    (hι : ∀ u : (Place.localField K w)ˣ, ι.hom (Additive.ofMul u)
      = Additive.ofMul (Place.localAlgebraMapUnits w' w hw u)) :
    ∃ ι' : Rep.res f (localUnitsSubP k K w) ⟶ localUnitsSubP k L w',
      Rep.resMap f (localUnitsInclP k K w) ≫ ι = ι' ≫ localUnitsInclP k L w' := by
  classical
  have hψ' : ∀ u : ↥(Place.localUnits K w),
      (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom (Additive.ofMul u)
        = Additive.ofMul (Place.localAlgebraMapUnits w' w hw u.1) := by
    intro u
    rw [Rep.comp_apply, Rep.resMap_hom_apply]
    exact hι (↑u : (Place.localField K w)ˣ)
  let gfun : Additive ↥(Place.localUnits K w) → Additive ↥(Place.localUnits L w') := fun a =>
    Additive.ofMul ⟨Place.localAlgebraMapUnits w' w hw (Additive.toMul a).1,
      NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits hw
        (Additive.toMul a).2⟩
  have hgf : ∀ a : Additive ↥(Place.localUnits K w),
      (localUnitsInclP k L w').hom (gfun a)
        = (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom a := by
    intro a
    have h1 : (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom a
        = Additive.ofMul (Place.localAlgebraMapUnits w' w hw (Additive.toMul a).1) := by
      rw [show a = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm]
      exact hψ' (Additive.toMul a)
    calc (localUnitsInclP k L w').hom (gfun a)
        = Additive.ofMul (Place.localAlgebraMapUnits w' w hw (Additive.toMul a).1) := rfl
      _ = (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom a := h1.symm
  have hinj : ∀ {a b : Additive ↥(Place.localUnits L w')},
      (localUnitsInclP k L w').hom a = (localUnitsInclP k L w').hom b → a = b := by
    intro a b h
    apply Additive.toMul.injective
    exact Subtype.ext (Additive.toMul.injective h)
  have hadd : ∀ a b : Additive ↥(Place.localUnits K w), gfun (a + b) = gfun a + gfun b := by
    intro a b
    refine hinj ?_
    calc (localUnitsInclP k L w').hom (gfun (a + b))
        = (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom (a + b) := hgf (a + b)
      _ = (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom a
            + (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom b := map_add _ a b
      _ = (localUnitsInclP k L w').hom (gfun a) + (localUnitsInclP k L w').hom (gfun b) := by
          rw [hgf a, hgf b]
      _ = (localUnitsInclP k L w').hom (gfun a + gfun b) := (map_add _ _ _).symm
  have hsmul : ∀ (n : Coeff) (a : Additive ↥(Place.localUnits K w)),
      gfun (n • a) = n • gfun a := by
    intro n a
    refine hinj ?_
    calc (localUnitsInclP k L w').hom (gfun (n • a))
        = (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom (n • a) := hgf (n • a)
      _ = n • (Rep.resMap f (localUnitsInclP k K w) ≫ ι).hom a := map_smul _ n a
      _ = n • (localUnitsInclP k L w').hom (gfun a) := by rw [hgf a]
      _ = (localUnitsInclP k L w').hom (n • gfun a) := (map_smul _ n _).symm
  have hintw : ∀ (σ : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w'))
      (a : Additive ↥(Place.localUnits K w)),
      gfun (((Rep.res f (localUnitsSubP k K w)).ρ σ) a)
        = ((localUnitsSubP k L w').ρ σ) (gfun a) := by
    intro σ a
    refine hinj ?_
    calc (localUnitsInclP k L w').hom (gfun (((Rep.res f (localUnitsSubP k K w)).ρ σ) a))
        = (Rep.resMap f (localUnitsInclP k K w) ≫ ι)
            (((Rep.res f (localUnitsSubP k K w)).ρ σ) a) :=
          hgf (((Rep.res f (localUnitsSubP k K w)).ρ σ) a)
      _ = (localUnitsK (k := k) (K := L) w').ρ σ
            ((Rep.resMap f (localUnitsInclP k K w) ≫ ι) a) :=
          Rep.hom_comm_apply (Rep.resMap f (localUnitsInclP k K w) ≫ ι) σ a
      _ = (localUnitsK (k := k) (K := L) w').ρ σ
            ((localUnitsInclP k L w').hom (gfun a)) := by rw [hgf a]
      _ = (localUnitsInclP k L w').hom (((localUnitsSubP k L w').ρ σ) (gfun a)) :=
          (Rep.hom_comm_apply (localUnitsInclP k L w') σ (gfun a)).symm
  let ι' : Rep.res f (localUnitsSubP k K w) ⟶ localUnitsSubP k L w' :=
    Rep.ofHom
      { toFun := gfun
        map_add' := hadd
        map_smul' := hsmul
        isIntertwining' := fun σ => LinearMap.ext (hintw σ) }
  have hι'_hom : ∀ a : ↑(Rep.res f (localUnitsSubP k K w)), (Rep.Hom.hom ι') a = gfun a :=
    fun a => rfl
  refine ⟨ι', ?_⟩
  apply Rep.hom_ext
  ext a
  change (Rep.Hom.hom (Rep.resMap f (localUnitsInclP k K w) ≫ ι)) a
      = (Rep.Hom.hom (ι' ≫ localUnitsInclP k L w')) a
  conv_rhs => rw [Rep.comp_apply]
  rw [hι'_hom a]
  exact (hgf a).symm

/-- **The local units map sends unramified classes to unramified classes.** -/
private theorem isUnramifiedExt_extRes_comp_mk0 {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] (u : Place K) (w : Place L) (hu : Place.LiesOver w u)
    (f : decompK (k := k) w →* decompK (k := k) u)
    (hf : ∀ σ, ((f σ : decompK (k := k) u) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) (K := K) u) ⟶ localUnitsK (k := k) (K := L) w)
    (hι : ∀ x : (Place.localField K u)ˣ, ι.hom (Additive.ofMul x)
      = Additive.ofMul (Place.localAlgebraMapUnits w u hu x))
    {M : Rep Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext (Rep.res (decompK (k := k) u).subtype M)
      (localUnitsK (k := k) (K := K) u) r)
    (hz : IsUnramifiedExt (k := k) (K := K) u z) :
    IsUnramifiedExt (k := k) (K := L) w
      ((extRes f z).comp (Abelian.Ext.mk₀ ι) (add_zero r)) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hz
  obtain ⟨ι', hfac⟩ := factorLocalUnitsIncl u w hu f ι hι
  refine ⟨(extRes f z₀).comp (Abelian.Ext.mk₀ ι') (add_zero r), ?_⟩
  have h1 : extRes f (z₀.comp (Abelian.Ext.mk₀ (localUnitsInclP k K u)) (add_zero r))
      = (extRes f z₀).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor f).map (localUnitsInclP k K u))) (add_zero r) := by
    have h := Abelian.Ext.mapExactFunctor_comp (F := Rep.resFunctor f) z₀
      (Abelian.Ext.mk₀ (localUnitsInclP k K u)) (add_zero r)
    rw [Abelian.Ext.mapExactFunctor_mk₀] at h
    exact h
  rw [hz₀, h1]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero (extRes f z₀)
        (Abelian.Ext.mk₀ ((Rep.resFunctor f).map (localUnitsInclP k K u)))
        (Abelian.Ext.mk₀ ι) (add_zero r),
      Abelian.Ext.mk₀_comp_mk₀]
  have hmap : ((Rep.resFunctor f).map (localUnitsInclP k K u)) ≫ ι
      = Rep.resMap f (localUnitsInclP k K u) ≫ ι := rfl
  rw [hmap, hfac, ← Abelian.Ext.mk₀_comp_mk₀ ι' (localUnitsInclP k L w)]
  exact (Abelian.Ext.comp_assoc_of_second_deg_zero (extRes f z₀) (Abelian.Ext.mk₀ ι')
    (Abelian.Ext.mk₀ (localUnitsInclP k L w)) (add_zero r)).symm

/-- **E9c, transport of unramifiedness along the level map `K → L`.** -/
private theorem e9c_transport_unram_aux {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
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
  rw [hmain]
  exact isUnramifiedExt_extRes_comp_mk0 u w hw (decompKRestrict k K L u w hw)
    (fun σ => decompKRestrict_coe k K L u w hw σ) ψ hψ _ hz

/-- **E9c, the local vanishing criterion for the global pairing value.**

Let `k ⊆ K ⊆ L ⊆ Ω`, `L/k` finite Galois, `M` a finite `Gal(K/k)`-module, `h ∈ H¹(Gal(L/k), res M)`
and `y ∈ Ext¹_G(M, 𝕀_K)`.  Suppose that `y` vanishes at every place of a set `T` of places of `K`
and is unramified at every place outside `T`, and that every place `w` of `L` whose place below lies
outside `T` is a finite place of ramification index one over `k`.  Then the global pairing value
`phiAt (extToClasses y) h ∈ H²(Gal(L/k), C_L)` vanishes. -/
theorem e9c_phiAt_eq_zero_of_local {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (h : extH (Rep.res (galRes k K L) M) 1)
    (T : Set (Place K))
    (y : Abelian.Ext M (Work.SSGRoute.idelesRepP k K) 1)
    (hTz : ∀ u ∈ T, extLoc (k := k) (K := K) u y = 0)
    (hTunr : ∀ u : Place K, u ∉ T →
      IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u y))
    (hram : ∀ w : Place L, (∀ u ∈ T, ¬ Place.LiesOver w u) →
      ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
        (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)),
        w = NK.GlobalCFT.Place.ofFinite q ∧ q.asIdeal.LiesOver Q.asIdeal ∧
          q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    phiAt (k := k) (K := K) (L := L) (extToClasses y) h = 0 := by
  classical
  -- Step 1: idèle lifting.
  rw [phiAt_extToClasses_eq_idleRepMap k K L M y h]
  -- Step 2: E2 injectivity at level `L`.
  have hW : levelPair (galRes k K L) (idleRepMap k K L) y h = 0 := by
    refine extIdele_localisation_injective (k := k) (L := L)
      (levelPair (galRes k K L) (idleRepMap k K L) y h) ?_
    intro w
    rw [extRes_eq_extHRestrict]
    change extLoc (k := k) (K := L) w (levelPair (galRes k K L) (idleRepMap k K L) y h) = 0
    rw [extLoc_levelPair_idleRepMap_eq k K L M y h w]
    obtain ⟨u, hu_lo⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w
    by_cases huT : u ∈ T
    · -- vanishing at `u`
      have hz : extLoc (k := k) (K := L) w
          ((extRes (galRes k K L) y).comp
            (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero 1)) = 0 :=
        e9c_transport_zero y u w hu_lo (hTz u huT)
      rw [hz]
      exact yonedaPair_zero _
    · -- unramified at `u`
      have hnot : ∀ u' ∈ T, ¬ Place.LiesOver w u' := by
        intro u' hu'T hlo
        have huu' : u = u' := place_liesOver_unique w hu_lo hlo
        rw [← huu'] at hu'T
        exact huT hu'T
      obtain ⟨q, Q, hw_eq, hq_lo, hq_ram⟩ := hram w hnot
      have hunr_w : IsUnramifiedExt (k := k) (K := L) w
          (extLoc (k := k) (K := L) w
            ((extRes (galRes k K L) y).comp
              (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero 1))) :=
        e9c_transport_unram_aux y u w hu_lo (hTunr u huT)
      have hpair : IsUnramifiedExt (k := k) (K := L) w
          (yonedaPair
            (extLoc (k := k) (K := L) w
              ((extRes (galRes k K L) y).comp
                (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero 1)))
            (extHRestrict (decompK (k := k) (K := L) w) h)) :=
        e9c_unram_pairing w _ h hunr_w
      subst hw_eq
      exact eq_zero_of_isUnramifiedExt_of_unramified k L q Q hq_lo hq_ram _ hpair
  rw [hW, Abelian.Ext.zero_comp]

end Work.SSGRoute
