import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.NK.CFTLib.HRclean.T3Clean
import Submission.NK.CFTLib.HRclean.T4Clean
import Submission.NK.CFTLib.HRclean.existsCycClassOfEqCopy
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrimeOdd
import Submission.NK.CFTLib.cyclotomicCruxAt_of_coprime
import Submission.NK.NUV2.ChebAux.Transfer.PlaceAux

/-!
# CLEAN ASSEMBLY (agent H-): the Brauer transfer and Hilbert reciprocity, cycle-free

The contents of `Submission/Work/CFTLib/HRdescent/transferMain.lean` (the class-level Brauer
transfer, the one-place transfer step and the crux `HilbertReciprocityOnePlace`) with all imports
redirected to the clean copies in this directory, so that the deliverable
`Submission/Work/CFTLib/hilbertReciprocity_cyclic.lean` can import them without an import cycle
(see `README.md`).
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.CFTLib.HRclean.Transfer

open NK.GlobalCFT CategoryTheory

/-! ## The localisation of the level inflation

The "hard" direction of `loc_ŵ(inf β) = 0 ↔ loc_w β = 0`: it is the injectivity of the local level
map `NK.CFTLib.HRdescent.localLevelMap_injective`, transported along the naturality square
`NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits` and the identity
`NK.CFTLib.IdeleHasse.Descent.inflation_eq_unitsLevelMapTower`. -/

theorem locUnits_inflation_eq_zero_iff {K M E : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (β : groupCohomology (NK.HassePrinciple.unitsRep K M) 2)
    (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom β) = 0
      ↔ (NK.HassePrinciple.locUnits K M w).hom β = 0 :=
  NK.CFTLib.HRclean.T4.locUnits_inflation_eq_zero_iff (K := K) (M := M) (E := E) β w ŵ hw

/-! ## The vanishing of the cyclic class of `x` at the level `L/K` (the Brauer transfer) -/

theorem cycClass_eq_zero_of_transfer_main {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L]
    [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E]
    [IsScalarTower K M E] [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ y : Kˣ,
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x = 0 := by
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  haveI : IsGalois L E := IsGalois.tower_top_of_isGalois K L E
  haveI : IsCyclic (L ≃ₐ[K] L) := hcycL
  haveI : IsCyclic (M ≃ₐ[K] M) := hcycM
  obtain ⟨gM, hgM⟩ := hcycM.exists_generator
  -- the translation identity (T1): the level-`E/M` class of `x`
  obtain ⟨g', hg', hg'eq⟩ := NK.CFTLib.HRclean.Cheb.cycClassOf_translation
    (K := K) (L := L) (M := M) (E := E) hgen g hg x
  haveI : IsCyclic (E ≃ₐ[M] E) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g', (Subgroup.eq_top_iff' _).mpr hg'⟩
  -- the image of `x` in `Mˣ`
  set x'M : Mˣ := Units.map (algebraMap K M).toMonoidHom x with hx'M
  -- the localisation dictionaries in `Place` form
  have dictL : ∀ v' : NK.GlobalCFT.Place L,
      (NK.HassePrinciple.locUnits K L v').hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 ↔
        NK.CFTLib.IdeleHasse.localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') x ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') := by
    intro v'
    rcases NK.GlobalCFT.Place.liesOver_iff v'
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) v') |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder v') with
      ⟨w', v'', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.HRclean.Dict.localNormSubgroup_iff_cycClass_infinite
        (K := K) (F := L) g hg v'' w' h3 x
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := K) (F := L) g hg Q q h3 x
  have dictEM : ∀ q : NK.GlobalCFT.Place E,
      (NK.HassePrinciple.locUnits M E q).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := M) (F := E) g' hg' x'M) = 0 ↔
        NK.CFTLib.IdeleHasse.localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) x'M ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) := by
    intro q
    rcases NK.GlobalCFT.Place.liesOver_iff q
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) (L := E) q) |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder q) with
      ⟨w', v'', h1, h2, h3⟩ | ⟨qq, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.HRclean.Dict.localNormSubgroup_iff_cycClass_infinite
        (K := M) (F := E) g' hg' v'' w' h3 x'M
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := M) (F := E) g' hg' Q qq h3 x'M
  -- STEP A: the restriction of the level-`E/K` class of `x` to `Gal(E/M)` vanishes
  have hres : (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
      ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
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
    have hvLvK : NK.GlobalCFT.Place.LiesOver vL vK := by
      have h := NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (NK.NUV2.ChebAux.Transfer.place_liesOver_trans (L := L) hŵL
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder vL)) hŵK
      rw [show vK = NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := L) vL from h.symm]
      exact NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder vL
    by_cases hv0 : vK = v₀
    · -- the case of the omitted place `v₀`
      rw [show (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
            ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
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
      exact NK.CFTLib.HRclean.Cheb.locUnits_res_inflation_eq_zero
        (K := K) (L := L) (M := M) (E := E) g hg x ŵ
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ) hŵL hcL
  -- the descent to the level `M/K` (inflation–restriction exactness + periodicity), (T3)
  have hT3 : ∀ (g₀ : M ≃ₐ[K] M) (hg₀ : ∀ σ : M ≃ₐ[K] M, σ ∈ Subgroup.zpowers g₀)
      (α : groupCohomology (NK.HassePrinciple.unitsRep K E) 2),
      (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom α = 0 →
        ∃ b : Kˣ, α = (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := M) g₀ hg₀ b) :=
    fun g₀ hg₀ α hα => NK.CFTLib.HRclean.T3.exists_cycClassOf_of_res_eq_zero
      (K := K) (L := L) (M := M) (E := E) hgen g₀ hg₀ α hα
  -- STEP B: descend to the level `M/K`
  obtain ⟨b, hb⟩ := hT3 gM hgM _ hres
  -- the level-`M` class of `b`
  set β : groupCohomology (NK.HassePrinciple.unitsRep K M) 2 :=
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := M) gM hgM b with hβ
  have dictMK : ∀ w : NK.GlobalCFT.Place M,
      (NK.HassePrinciple.locUnits K M w).hom β = 0 ↔
        NK.CFTLib.IdeleHasse.localImageAt
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) b ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M)
            (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) := by
    intro w
    rcases NK.GlobalCFT.Place.liesOver_iff w
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w) |>.mp
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) with
      ⟨w', v'', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · rw [h2, h1]
      exact NK.CFTLib.HRclean.Dict.localNormSubgroup_iff_cycClass_infinite
        (K := K) (F := M) gM hgM v'' w' h3 b
    · rw [h2, h1]
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := K) (F := M) gM hgM Q q h3 b
  -- STEP C: the localisations of `β` at the places away from `v₀` vanish
  have hlocβ : ∀ w : NK.GlobalCFT.Place M, ¬ NK.GlobalCFT.Place.LiesOver w v₀ →
      (NK.HassePrinciple.locUnits K M w).hom β = 0 := by
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
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) = 0 :=
      NK.CFTLib.HRclean.DescentInf.locUnits_inflation_eq_zero_of_loc_eq_zero
        (K := K) (L := L) (E := E)
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)
        (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) (L := E) ŵ) ŵ hŵL hcL
    have hT4 := locUnits_inflation_eq_zero_iff (K := K) (M := M) (E := E) β w ŵ hŵw
    refine (hT4.mp ?_)
    rw [← hb]
    exact hlocα
  -- STEP D: `hM` supplies the missing local norm at `v₀`
  have hb0 : NK.CFTLib.IdeleHasse.localImageAt v₀ b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀ :=
    hM b (fun v hv => by
      obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := M) v
      have hwne : ¬ NK.GlobalCFT.Place.LiesOver w v₀ := by
        intro h
        exact hv (NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hw h)
      have h1 := (dictMK w).mp (hlocβ w hwne)
      rwa [NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) hw] at h1)
  -- STEP E: `β = 0` by the Hasse principle at the level `M/K`
  have hβ0 : β = 0 := by
    refine (NK.GlobalCFTdeep.hbnUnits (F := K) (E := M)) β (fun w => ?_)
    by_cases hw : NK.GlobalCFT.Place.LiesOver w v₀
    · have hwk : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w = v₀ :=
        NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
          (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w) hw
      exact (dictMK w).mpr (hwk ▸ hb0)
    · exact hlocβ w hw
  -- STEP F: the level-`E/K` class of `x` vanishes
  have hα0 : (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0 := by
    rw [hb, hβ0, map_zero]
  -- STEP G: `x` is a local norm for `L/K` everywhere, hence the class vanishes
  refine (NK.GlobalCFTdeep.hbnUnits (F := K) (E := L))
    (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) (fun v' => ?_)
  by_cases hv' : NK.GlobalCFT.Place.LiesOver v' v₀
  · obtain ⟨ŵ, hŵv'⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := L) (L := E) v'
    have hloc : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) = 0 := by
      rw [hα0, map_zero]
    have hT4' := locUnits_inflation_eq_zero_iff (K := K) (M := L) (E := E)
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) v' ŵ hŵv'
    exact hT4'.mp hloc
  · refine (dictL v').mpr (hx _ (fun h => hv' ?_))
    rw [← h]
    exact NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder v'

/-! ## The one-place Brauer transfer -/

theorem transferOnePlace_main {K L M E : Type} [Field K] [NumberField K] [Field L]
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
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ :=
  NK.CFTLib.HRclean.Final.auxDescentTransfer_of_cycClassOf_eq_zero (K := K) (L := L) hcycL x v₀
    (fun g hg => cycClass_eq_zero_of_transfer_main (K := K) (L := L) (M := M) (E := E)
      hgen hcycL hcycM x v₀ hM hx hv₀ g hg)

/-! ## Hilbert reciprocity for cyclic extensions -/

theorem hilbertReciprocityOnePlace_main : NK.CFTLib.HilbertReciprocityOnePlace := by
  intro K L _ _ _ _ _ _ _ _ a v₀ h
  obtain ⟨M, E, hFM, hNFM, hFE, hNFE, hAKM, hAKE, hALE, hAME, hTLE, hTME, hFDM, hFDE,
      hGalM, hGalE, hCycM, m, hm, hm2, hCycl, hgen, hcop, hloc⟩ :=
    NK.CFTLib.HRdescent.localConditionCyclotomicPrimeOdd (K := K) (L := L) (inferInstance) v₀
  letI : Algebra K M := hAKM
  letI : Algebra K E := hAKE
  letI : Algebra L E := hALE
  letI : Algebra M E := hAME
  letI : IsScalarTower K L E := hTLE
  letI : IsScalarTower K M E := hTME
  letI : FiniteDimensional K M := hFDM
  letI : FiniteDimensional K E := hFDE
  letI : IsGalois K M := hGalM
  letI : IsGalois K E := hGalE
  haveI : IsCyclic (M ≃ₐ[K] M) := hCycM
  haveI : IsCyclotomicExtension {m} K M := hCycl
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  haveI : IsCyclic (L ≃ₐ[K] L) := inferInstance
  have hM := fun y : Kˣ => NK.CFTLib.cyclotomicCruxAt_of_coprime (K := K) (M := M)
    m hm hm2 v₀ hcop y
  exact transferOnePlace_main (K := K) (L := L) (M := M) (E := E) hgen inferInstance hCycM v₀
    hM a h (fun w hw => hloc a w hw)

end NK.CFTLib.HRclean.Transfer
