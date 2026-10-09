import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.HR.transferAt
import Submission.NK.CFTLib.HR.TransferAux.FinalStep
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
import Submission.NK.NUV2.ChebAux.Transfer.Defs
import Submission.NK.NUV2.ChebAux.Transfer.PlaceAux
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.ChebAux.isCyclic_gal_of_compositum
import Submission.NK.NUV2.ARL.HR.TransferSupport
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.CFTLib.IdeleHasse.Descent.locUnits_inflation_eq_zero_of_loc_eq_zero
import Submission.NK.CFTLib.HR.TransferAux.exists_inflation_eq_of_resToGal_eq_zero
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.CFTLib.HR

open NK.CFTLib.IdeleHasse

/-- **The periodicity surjectivity at a cyclic level**: every class of `H²(Gal(M/K), Mˣ)` is the
cyclic class of a global element `b ∈ Kˣ` (periodicity together with the Galois descent
`(Mˣ)^{Gal(M/K)} = Kˣ`). -/
private theorem exists_cycClassOf_eq_period {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (g : M ≃ₐ[K] M) (hg : ∀ σ : M ≃ₐ[K] M, σ ∈ Subgroup.zpowers g)
    (β : groupCohomology (NK.HassePrinciple.unitsRep K M) 2) :
    ∃ b : Kˣ, NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := M) g hg b = β := by
  obtain ⟨a, ha, hcls⟩ := NK.CFTLib.IdeleHasse.Descent.exists_eq_cycClass
    (NK.HassePrinciple.unitsRep K M) g hg β
  set a' : Mˣ := Additive.toMul a with ha'_def
  have hfix : ∀ σ : M ≃ₐ[K] M, Units.map σ.toMonoidHom a' = a' := by
    intro σ
    have h1 := ha σ
    have h2 : (NK.HassePrinciple.unitsRep K M).ρ σ a
        = Additive.ofMul (Units.map σ.toMonoidHom (Additive.toMul a)) := rfl
    rw [h2, ← ha'_def] at h1
    exact Additive.ofMul.injective h1
  have hfix' : ∀ σ : M ≃ₐ[K] M, σ (a' : M) = (a' : M) := by
    intro σ
    have h1 := hfix σ
    have h2 := congrArg (fun u : Mˣ => (u : M)) h1
    rw [Units.coe_map] at h2
    exact h2
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := M)
    (a' : M)).mpr hfix'
  have hk0 : k ≠ 0 := by
    intro h0
    have h1 : (a' : M) = 0 := by rw [← hk, h0]; simp
    exact a'.ne_zero h1
  refine ⟨Units.mk0 k hk0, ?_⟩
  have h3 : Units.map (algebraMap K M).toMonoidHom (Units.mk0 k hk0) = a' := by
    apply Units.ext
    rw [Units.coe_map]
    simpa using hk
  have hunits : NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := M)
      (Units.mk0 k hk0) = a := by
    rw [NK.CFTLib.IdeleHasse.Descent.unitsImage, h3, ha'_def]
    rfl
  rw [NK.CFTLib.IdeleHasse.Descent.cycClassOf]
  subst hunits
  exact hcls

/-- **The local injectivity of the local level map**, in the form used by the transfer: if the
localisation at `ŵ` of the level inflation of `γ` vanishes, then the localisation of `γ` at the
place `w` below `ŵ` vanishes.  This is the "local Hilbert 90"/norm-tower step of the Brauer
descent. -/
private theorem localLevelInjectiveAux {K M E : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w)
    (γ : groupCohomology (NK.HassePrinciple.unitsRep K M) 2)
    (hγ : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.NUV2.ARL.HR.inflation (K := K) (L := M) (E := E)).hom γ) = 0) :
    (NK.HassePrinciple.locUnits K M w).hom γ = 0 := by
  rw [show (NK.NUV2.ARL.HR.inflation (K := K) (L := M) (E := E))
      = NK.NUV2.LC.unitsLevelMapTower (F := K) (L := M) (M := E)
      from NK.CFTLib.IdeleHasse.Descent.inflation_eq_unitsLevelMapTower] at hγ
  have hsq := NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits (F := K) (L := M) (M := E) hw
  have h2 : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := K) (L := M) (M := E)) γ)
      = (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) hw).hom
          ((NK.HassePrinciple.locUnits K M w).hom γ) := by
    have hh := congrArg (fun f : groupCohomology (NK.HassePrinciple.unitsRep K M) 2 ⟶
        groupCohomology (NK.HassePrinciple.localUnitsRep K E ŵ) 2 => f.hom γ) hsq
    simpa using hh
  rw [h2] at hγ
  exact NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
    (K := K) (M := M) (E := E) w ŵ hw _ hγ

/-- **The Brauer transfer at one place: the cyclic class of `x` at the level `L/K` vanishes.**

This is the class-level form of `transferOnePlace` (`NK.CFTLib.IdeleHasse.Descent.cycClassOf` of
`x` at the cyclic level `L/K`), proved by the Brauer descent: the class is inflated to the level
`E/K`, restricted to `Gal(E/M)` (where it dies by the Hasse–Brauer–Noether theorem, using the local
conditions `hx` away from `v₀` and `hv₀` at the places over `v₀` in the form of the localisation
dictionaries), descended to the level `M/K` by the inflation–restriction exactness, written as the
cyclic class of some `b ∈ Kˣ`, shown to be a local norm for `M/K` at every `v ≠ v₀` (using the
local injectivity of the local level map), and finally killed by `hM` and the Hasse principle at the
level `M/K`. -/
private theorem cycClassVanishing {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ y : Kˣ,
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        localImageAt v y ∈ localNormSubgroup (K := K) (L := M) v) →
      localImageAt v₀ y ∈ localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      localImageAt v x ∈ localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        localNormSubgroup (K := M) (L := E) w)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x = 0 := by
  classical
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  haveI : IsGalois L E := IsGalois.tower_top_of_isGalois K L E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  haveI hcycL' : IsCyclic (L ≃ₐ[K] L) := hcycL
  haveI hcycM' : IsCyclic (M ≃ₐ[K] M) := hcycM
  obtain ⟨gM, hgM⟩ := hcycM'.exists_generator
  -- the translation identity: the level-`E/M` class of `x`
  obtain ⟨g', hg', hg'eq⟩ := NK.NUV2.ChebAux.Transfer.cycClassOf_translation
    (K := K) (L := L) (M := M) (E := E) hgen g hg x
  haveI hcycEM : IsCyclic (E ≃ₐ[M] E) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g', (Subgroup.eq_top_iff' _).mpr hg'⟩
  set x'M : Mˣ := Units.map (algebraMap K M).toMonoidHom x with hx'M
  -- the localisation dictionaries, in `Place` form
  have dictL : ∀ v' : NK.GlobalCFT.Place L,
      (NK.HassePrinciple.locUnits K L v').hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 ↔
        localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') x ∈
          localNormSubgroup (K := K) (L := L)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') := by
    intro v'
    rcases NK.GlobalCFT.Place.liesOver_iff v'
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder v') with
      ⟨w', v'', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
        (K := K) (F := L) g hg v'' w' h3 x
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := K) (F := L) g hg Q q h3 x
  have dictEM : ∀ q : NK.GlobalCFT.Place E,
      (NK.HassePrinciple.locUnits M E q).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := M) (F := E) g' hg' x'M) = 0 ↔
        localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) x'M ∈
          localNormSubgroup (K := M) (L := E)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) := by
    intro q
    rcases NK.GlobalCFT.Place.liesOver_iff q
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder q) with
      ⟨w', v'', h1, h2, h3⟩ | ⟨qq, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
        (K := M) (F := E) g' hg' v'' w' h3 x'M
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := M) (F := E) g' hg' Q qq h3 x'M
  -- STEP A: the restriction of the level-`E/K` class of `x` to `Gal(E/M)` vanishes
  have hres : (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom
      ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) = 0 := by
    refine (NK.GlobalCFTdeep.hbnUnits (F := M) (E := E)) _ (fun ŵ => ?_)
    set wM : NK.GlobalCFT.Place M :=
      NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) ŵ with hwMdef
    set vK : NK.GlobalCFT.Place K :=
      NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := E) ŵ with hvKdef
    set vL : NK.GlobalCFT.Place L :=
      NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ with hvLdef
    have hŵM : NK.GlobalCFT.Place.LiesOver ŵ wM :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    have hŵK : NK.GlobalCFT.Place.LiesOver ŵ vK :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    have hŵL : NK.GlobalCFT.Place.LiesOver ŵ vL :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    have hwMvK : NK.GlobalCFT.Place.LiesOver wM vK := by
      have h := NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (NK.NUV2.ChebAux.Transfer.place_liesOver_trans (L := M) hŵM
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder wM)) hŵK
      rw [show vK = NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) wM from h.symm]
      exact NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder wM
    by_cases hv0 : vK = v₀
    · -- the case of the omitted place `v₀`
      rw [show (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom
            ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
              (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x))
          = NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := M) (F := E) g' hg' x'M
        from hg'eq]
      exact (dictEM ŵ).mpr (hv₀ wM (hv0 ▸ hwMvK))
    · -- a place away from `v₀`
      have hcL : (NK.HassePrinciple.locUnits K L vL).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
        refine (dictL vL).mpr ?_
        have hunder : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) vL = vK :=
          NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
            (NK.NUV2.ChebAux.Transfer.place_liesOver_trans (L := L) hŵL
              (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder vL)) hŵK
        rw [hunder]
        exact hx vK hv0
      exact NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
        (K := K) (L := L) (M := M) (E := E) g hg x ŵ vL hŵL hcL
  -- STEP B: descend to the level `M/K` (inflation–restriction exactness + periodicity)
  obtain ⟨β, hβ⟩ := NK.CFTLib.HR.TransferAux.exists_inflation_eq_of_resToGal_eq_zero
    (K := K) (M := M) (E := E)
    ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) hres
  obtain ⟨b, hb⟩ := exists_cycClassOf_eq_period (K := K) (M := M) gM hgM β
  set β' : groupCohomology (NK.HassePrinciple.unitsRep K M) 2 :=
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := M) gM hgM b with hβ'
  have hββ : β = β' := hb.symm
  have dictMK : ∀ w : NK.GlobalCFT.Place M,
      (NK.HassePrinciple.locUnits K M w).hom β' = 0 ↔
        localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) b ∈
          localNormSubgroup (K := K) (L := M)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) := by
    intro w
    rcases NK.GlobalCFT.Place.liesOver_iff w
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) with
      ⟨w', v'', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
        (K := K) (F := M) gM hgM v'' w' h3 b
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := K) (F := M) gM hgM Q q h3 b
  -- STEP C: the localisations of `β` at the places away from `v₀` vanish
  have hlocβ : ∀ w : NK.GlobalCFT.Place M, ¬ NK.GlobalCFT.Place.LiesOver w v₀ →
      (NK.HassePrinciple.locUnits K M w).hom β' = 0 := by
    intro w hw
    obtain ⟨ŵ, hŵw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := M) (L := E) w
    have hŵL : NK.GlobalCFT.Place.LiesOver ŵ
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ) :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    have hwK : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w ≠ v₀ := by
      intro h
      exact hw (h ▸ NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w)
    have hbelow : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L)
          (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ)
        = NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w :=
      NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (NK.NUV2.ChebAux.Transfer.place_liesOver_trans (L := L) hŵL
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ)))
        (NK.NUV2.ChebAux.Transfer.place_liesOver_trans (L := M) hŵw
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w))
    have hcL : (NK.HassePrinciple.locUnits K L
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ)).hom
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
      refine (dictL _).mpr ?_
      rw [hbelow]
      exact hx _ (fun h => hwK h)
    have hlocα : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) = 0 := by
      rw [← ConcreteCategory.comp_apply,
        NK.NUV2.ARL.HR.locUnits_inflation_eq (K := K) (M := L) (E := E) _ ŵ hŵL,
        ConcreteCategory.comp_apply, hcL, map_zero]
    refine localLevelInjectiveAux (K := K) (M := M) (E := E) w ŵ hŵw β' ?_
    rw [← hββ, hβ]
    exact hlocα
  -- STEP D: `hM` supplies the missing local norm at `v₀`
  have hb0 : localImageAt v₀ b ∈ localNormSubgroup (K := K) (L := M) v₀ :=
    hM b (fun v hv => by
      obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := M) v
      have hwne : ¬ NK.GlobalCFT.Place.LiesOver w v₀ := by
        intro h
        exact hv (NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hw h)
      have h1 := (dictMK w).mp (hlocβ w hwne)
      rwa [NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) hw] at h1)
  -- STEP E: `β = 0` by the Hasse principle at the level `M/K`
  have hβ0 : β' = 0 := by
    refine (NK.GlobalCFTdeep.hbnUnits (F := K) (E := M)) β' (fun w => ?_)
    by_cases hw : NK.GlobalCFT.Place.LiesOver w v₀
    · have hwk : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w = v₀ :=
        NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) hw
      exact (dictMK w).mpr (hwk ▸ hb0)
    · exact hlocβ w hw
  have hα0 : (NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
    rw [← hβ, hββ, hβ0, map_zero]
  -- STEP F: `x` is a local norm for `L/K` everywhere, hence the class vanishes
  refine (NK.GlobalCFTdeep.hbnUnits (F := K) (E := L))
    (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) (fun v' => ?_)
  by_cases hv' : NK.GlobalCFT.Place.LiesOver v' v₀
  · obtain ⟨ŵ, hŵv'⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := L) (L := E) v'
    have hloc : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) = 0 := by
      rw [hα0, map_zero]
    exact localLevelInjectiveAux (K := K) (M := L) (E := E) v' ŵ hŵv' _ hloc
  · refine (dictL v').mpr (hx _ (fun h => hv' ?_))
    rw [← h]
    exact NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder v'

end NK.CFTLib.HR

namespace NK.CFTLib.HR

/-- **The transfer step of the Brauer descent** (Milne, *CFT*, VII §8).  See
`NK.CFTLib.HR.cycClassVanishing` for the class-level form. -/
theorem transferOnePlace {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ y : Kˣ,
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  classical
  obtain ⟨g, hg⟩ := hcycL.exists_generator
  have hc0 := cycClassVanishing (K := K) (L := L) (M := M) (E := E) hgen hcycL hcycM v₀ hM x hx hv₀ g hg
  obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := L) v₀
  have h0 : (NK.HassePrinciple.locUnits K L w).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
    rw [hc0]
    exact map_zero _
  rcases hw with ⟨w', v', rfl, rfl, hw'⟩ | ⟨q, Q, rfl, rfl, hq⟩
  · exact (NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
      (K := K) (F := L) g hg v' w' hw' x).mp h0
  · exact (NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
      (K := K) (F := L) g hg Q q hq x).mp h0

end NK.CFTLib.HR
