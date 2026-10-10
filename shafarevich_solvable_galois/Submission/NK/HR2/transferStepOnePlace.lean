import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.HR2.exists_cycClassOf_of_res_eq_zero
import Submission.NK.HR2.locUnits_inflation_eq_zero_iff
import Submission.NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The one-place Brauer transfer

`NK.HR2.transferStepOnePlace`: the transfer step of the Brauer descent of Hilbert reciprocity
(Milne, *CFT*, VII §8, Lemma 8.5 + Proposition 7.2 + Lemma 8.6) for one pair of cyclic levels.

Mathematically: let `K ⊆ L, M ⊆ E` with `E = L·M`, `L/K`, `M/K`, `E/K` Galois and `L/K`, `M/K`
cyclic.  Let `hM` be the "one place omitted" form of Hilbert reciprocity at the auxiliary level
`M/K`, let `x ∈ Kˣ` be a local norm from `L` at every place `v ≠ v₀` and a local norm from `E`
over `M` at every place of `M` over `v₀` (`hv₀`).  Then `x` is a local norm from `L` at `v₀`.

The proof is the cohomological (Brauer) transfer:

* `c := cycClassOf_{L/K} x ∈ H²(Gal(L/K), Lˣ)` is the cyclic class of `x`;
* `α := inflation_{L/K}(c) ∈ H²(Gal(E/K), Eˣ)`;
* the restriction of `α` to `Gal(E/M)` has vanishing localisation at every place of `E`
  (`HBNUnits M E`): at the places not over `v₀` this is `hx` + the level-change square
  (`locUnits_rhoRestrict_unitsInclRepM_eq`), at the places over `v₀` it is `hv₀` +
  the Brauer translation `cycClassOf_translation` and the localisation dictionary at the level
  `E/M`;
* inflation–restriction (`HBNUnits M E` ⟹ `res α = 0`; then the exactness of inflation–restriction)
  writes `α = inflation_{M/K}(β)` with `β = cycClassOf_{M/K} b` for some `b ∈ Kˣ`;
* for `v ≠ v₀` the localisation of `α` vanishes, and the injectivity of the *local* inflation
  (`locUnits_inflation_eq_zero_iff`) gives that `b` is a local norm from `M` at `v`; this and `hM`
  give that all localisations of `β` vanish, so `β = 0` by `HBNUnits K M`;
* hence `α = 0`, and the injectivity of the inflation at the level `L/K` (again
  `locUnits_inflation_eq_zero_iff`, now with `M := L`) gives that the localisation of `c` at `v₀`
  vanishes, which by the localisation dictionary is the conclusion.
-/

namespace NK.HR2

end NK.HR2

namespace NK.HR2

open NK.GlobalCFT CategoryTheory Representation

/-- The place-generic form of the localisation dictionary. -/
theorem localNormSubgroup_iff_cycClass_place {K F : Type} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] [IsCyclic (F ≃ₐ[K] F)]
    (g : F ≃ₐ[K] F) (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g)
    (r : NK.GlobalCFT.Place F) (v : NK.GlobalCFT.Place K)
    (hv : NK.GlobalCFT.Place.LiesOver r v) (y : Kˣ) :
    (NK.HassePrinciple.locUnits K F r).hom
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := F) g hg y) = 0 ↔
      NK.CFTLib.IdeleHasse.localImageAt v y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F) v := by
  rcases r with w' | q
  · rcases hv with ⟨w'', v', h1, h2, h3⟩ | ⟨Q, Q', h1, h2, h3⟩
    · obtain rfl : w' = w'' := NK.GlobalCFT.Place.ofInfinite_inj.mp h1
      obtain rfl : v = NK.GlobalCFT.Place.ofInfinite v' := h2
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_infinite
        (K := K) (F := F) g hg v' w' h3 y
    · exact absurd h1 (by simp)
  · rcases hv with ⟨w'', v', h1, h2, h3⟩ | ⟨Q, Q', h1, h2, h3⟩
    · exact absurd h1 (by simp)
    · obtain rfl : q = Q := NK.GlobalCFT.Place.ofFinite_inj.mp h1
      obtain rfl : v = NK.GlobalCFT.Place.ofFinite Q' := h2
      exact NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
        (K := K) (F := F) g hg Q' q h3 y

/-- If `ŵ` lies over `w` and also over `v`, then `w` lies over `v`. -/
theorem liesOver_of_liesOver_of_placeUnder {K L E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field E] [NumberField E] [Algebra K L] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] [FiniteDimensional K L] [FiniteDimensional L E] [FiniteDimensional K E]
    {ŵ : NK.GlobalCFT.Place E} {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place K}
    (hŵ : NK.GlobalCFT.Place.LiesOver ŵ w) (hv : NK.GlobalCFT.Place.LiesOver ŵ v) :
    NK.GlobalCFT.Place.LiesOver w v := by
  have h1 : NK.GlobalCFT.Place.LiesOver ŵ
      (NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) w) :=
    NK.NUV2.ChebAux.Transfer.place_liesOver_trans hŵ
      (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w)
  have h2 : NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) w = v :=
    NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 hv
  exact h2 ▸ (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w)

theorem transferStepOnePlace {K L M E : Type} [Field K] [NumberField K] [Field L]
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
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  haveI : FiniteDimensional L E := Module.Finite.of_restrictScalars_finite K L E
  have : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  have : IsGalois L E := IsGalois.tower_top_of_isGalois K L E
  haveI : IsCyclic (E ≃ₐ[M] E) := NK.NUV2.ChebAux.isCyclic_gal_of_compositum hgen hcycL
  obtain ⟨gL, hgL⟩ := hcycL.exists_generator
  obtain ⟨gM, hgM⟩ := hcycM.exists_generator
  let cL := NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) gL hgL x
  let α := (NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom cL
  -- (i) the localisation of the inflation vanishes away from `v₀`
  have hlocE : ∀ ŵ : NK.GlobalCFT.Place E, ¬ NK.GlobalCFT.Place.LiesOver ŵ v₀ →
      (NK.HassePrinciple.locUnits K E ŵ).hom α = 0 := by
    intro ŵ hŵ
    let r : NK.GlobalCFT.Place L := NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) ŵ
    have hr : NK.GlobalCFT.Place.LiesOver ŵ r :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    let v : NK.GlobalCFT.Place K := NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) r
    have hv : NK.GlobalCFT.Place.LiesOver r v :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder r
    have hvE : NK.GlobalCFT.Place.LiesOver ŵ v :=
      NK.NUV2.ChebAux.Transfer.place_liesOver_trans hr hv
    have hvv₀ : v ≠ v₀ := fun h => hŵ (h ▸ hvE)
    have hclL : (NK.HassePrinciple.locUnits K L r).hom cL = 0 :=
      (localNormSubgroup_iff_cycClass_place (K := K) (F := L) gL hgL r v hv x).mpr (hx v hvv₀)
    exact locUnits_inflation_eq_zero_of_loc_eq_zero cL r ŵ hr hclL
  -- (ii) the localisation of the restriction of `α` vanishes at the places over `v₀`
  have hlocRes₀ : ∀ ŵ : NK.GlobalCFT.Place E, NK.GlobalCFT.Place.LiesOver ŵ v₀ →
      (NK.HassePrinciple.locUnits M E ŵ).hom
        ((NK.NUV2.ChebAux.Transfer.resToGal K M E).hom α) = 0 := by
    intro ŵ hŵ
    obtain ⟨g', hg', htrans⟩ := NK.NUV2.ChebAux.Transfer.cycClassOf_translation
      (K := K) (L := L) (M := M) (E := E) hgen gL hgL x
    have hαeq : (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom α
        = NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := M) (F := E) g' hg'
            (Units.map (algebraMap K M).toMonoidHom x) := htrans
    rw [hαeq]
    let w : NK.GlobalCFT.Place M := NK.GlobalCFT.Norm.globalCFT_placeUnder (K := M) ŵ
    have hw : NK.GlobalCFT.Place.LiesOver ŵ w :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    have hwv₀ : NK.GlobalCFT.Place.LiesOver w v₀ :=
      liesOver_of_liesOver_of_placeUnder hw hŵ
    exact (localNormSubgroup_iff_cycClass_place (K := M) (F := E) g' hg' ŵ w hw
      (Units.map (algebraMap K M).toMonoidHom x)).mpr (hv₀ w hwv₀)
  -- (iii) the localisation of the restriction of `α` vanishes away from `v₀`
  have hlocRes : ∀ ŵ : NK.GlobalCFT.Place E, ¬ NK.GlobalCFT.Place.LiesOver ŵ v₀ →
      (NK.HassePrinciple.locUnits M E ŵ).hom
        ((NK.NUV2.ChebAux.Transfer.resToGal K M E).hom α) = 0 := by
    intro ŵ hŵ
    let r : NK.GlobalCFT.Place L := NK.GlobalCFT.Norm.globalCFT_placeUnder (K := L) ŵ
    have hr : NK.GlobalCFT.Place.LiesOver ŵ r :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder ŵ
    let v : NK.GlobalCFT.Place K := NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) r
    have hv : NK.GlobalCFT.Place.LiesOver r v :=
      NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder r
    have hvE : NK.GlobalCFT.Place.LiesOver ŵ v :=
      NK.NUV2.ChebAux.Transfer.place_liesOver_trans hr hv
    have hvv₀ : v ≠ v₀ := fun h => hŵ (h ▸ hvE)
    have hclL : (NK.HassePrinciple.locUnits K L r).hom cL = 0 :=
      (localNormSubgroup_iff_cycClass_place (K := K) (F := L) gL hgL r v hv x).mpr (hx v hvv₀)
    have h1 : (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom α
        = (groupCohomology.map (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E))
            (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2).hom cL := by
      have h2 := congrArg (fun (φ : groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
          groupCohomology (NK.HassePrinciple.unitsRep M E) 2) => φ.hom cL)
        (NK.NUV2.ChebAux.Transfer.resToGal_inflation_eq_map (K := K) (L := L) (M := M) (E := E))
      simpa only [ConcreteCategory.comp_apply] using h2
    rw [h1]
    have hsq : (NK.HassePrinciple.locUnits M E ŵ).hom
          ((groupCohomology.map (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E))
            (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2).hom cL)
        = (NK.NUV2.ChebAux.Transfer.localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ r hr).hom
            ((NK.HassePrinciple.locUnits K L r).hom cL) := by
      have h3 := congrArg (fun (φ : groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
          groupCohomology (NK.HassePrinciple.localUnitsRep M E ŵ) 2) => φ.hom cL)
        (NK.NUV2.ChebAux.Transfer.locUnits_rhoRestrict_unitsInclRepM_eq
          (K := K) (L := L) (M := M) (E := E) ŵ r hr)
      simpa only [ConcreteCategory.comp_apply] using h3
    rw [hsq, hclL, map_zero]
  -- (iv) `HBNUnits M E` gives `res α = 0`
  have hresα : (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom α = 0 :=
    (NK.GlobalCFTdeep.hbnUnits (F := M) (E := E)) _
      (fun ŵ => by
        by_cases h : NK.GlobalCFT.Place.LiesOver ŵ v₀
        · exact hlocRes₀ ŵ h
        · exact hlocRes ŵ h)
  -- (v) descent
  obtain ⟨b, hb⟩ := NK.HR2.exists_cycClassOf_of_res_eq_zero
    (K := K) (L := L) (M := M) (E := E) hgen gM hgM α hresα
  let β := NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := M) gM hgM b
  have hβ : α = (NK.NUV2.ARL.HR.inflation (K := K) (L := M) (E := E)).hom β := hb
  -- (vi) away from `v₀` the localisations of `β` vanish
  have hβloc : ∀ w : NK.GlobalCFT.Place M, ¬ NK.GlobalCFT.Place.LiesOver w v₀ →
      (NK.HassePrinciple.locUnits K M w).hom β = 0 := by
    intro w hw
    obtain ⟨ŵ, hŵ⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := M) (L := E) w
    have h1 : (NK.HassePrinciple.locUnits K E ŵ).hom α = 0 :=
      hlocE ŵ (fun h => hw (liesOver_of_liesOver_of_placeUnder hŵ h))
    refine (locUnits_inflation_eq_zero_iff (K := K) (M := M) (E := E) β w ŵ hŵ).mp ?_
    rw [← hβ]
    exact h1
  -- (vii) `hM` and the dictionary give the local norms at `v₀`
  have hbNorm : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v := by
    intro v hv
    obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := M) v
    have h1 : (NK.HassePrinciple.locUnits K M w).hom β = 0 :=
      hβloc w (fun h => hv (NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hw h))
    exact (localNormSubgroup_iff_cycClass_place (K := K) (F := M) gM hgM w v hw b).mp h1
  have hbNorm₀ : NK.CFTLib.IdeleHasse.localImageAt v₀ b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀ := hM b hbNorm
  have hβloc_all : ∀ w : NK.GlobalCFT.Place M, (NK.HassePrinciple.locUnits K M w).hom β = 0 := by
    intro w
    by_cases hw : NK.GlobalCFT.Place.LiesOver w v₀
    · exact (localNormSubgroup_iff_cycClass_place (K := K) (F := M) gM hgM w v₀ hw b).mpr hbNorm₀
    · exact hβloc w hw
  -- (viii) `β = 0` and hence `α = 0`
  have hβ0 : β = 0 := (NK.GlobalCFTdeep.hbnUnits (F := K) (E := M)) β hβloc_all
  have hα0 : α = 0 := by rw [hβ, hβ0, map_zero]
  -- (ix) the goal
  obtain ⟨r, hr⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := L) v₀
  obtain ⟨ŵ, hŵ⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := L) (L := E) r
  have hone : (NK.HassePrinciple.locUnits K E ŵ).hom α = 0 := by
    rw [hα0]; exact map_zero _
  have hclL : (NK.HassePrinciple.locUnits K L r).hom cL = 0 :=
    (locUnits_inflation_eq_zero_iff (K := K) (M := L) (E := E) cL r ŵ hŵ).mp hone
  exact (localNormSubgroup_iff_cycClass_place (K := K) (F := L) gL hgL r v₀ hr x).mp hclL

end NK.HR2
