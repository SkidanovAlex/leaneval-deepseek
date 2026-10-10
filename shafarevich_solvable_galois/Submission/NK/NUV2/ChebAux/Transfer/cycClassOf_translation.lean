import Mathlib.Tactic.Have
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.ChebAux.Transfer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Brauer translation of the cyclic class along a compositum

For a tower of number fields `K ⊆ L, M ⊆ E` with `E = L·M` (recorded by `hgen`), `L/K` cyclic,
`g` a generator of `Gal(L/K)` and `x ∈ Kˣ`, this file proves the "Brauer translation"

`res_{E/M}( inf_{E/K}( cycClass_{L/K} g x ) ) = cycClass_{E/M} g' (x)`

for a suitable generator `g'` of `Gal(E/M)`, where `res` is the restriction along
`Gal(E/M) ↪ Gal(E/K)` and `inf` the level inflation `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)`.

The two mathematical inputs are

* `Gal(E/M)` is cyclic and its canonical generator `g'` is the one with
  `rhoRestrict g' = g ^ m`, where `m·|Gal(E/M)| = |Gal(L/K)|` (`m = [L ⊓ M : K]`); this is
  `exists_generator_rhoRestrict`;
* the functoriality `map_cycClass` of the explicit cyclic cocycle
  (`NK.CFTLib.IdeleHasse.Descent.map_cycClass`), applied to the composite map
  `resToGal ≫ inflation = map rhoRestrict unitsInclRepM` of `inflation_comp_resToGal`.

The arithmetic content is exactly the compatibility `carry_comp` of the "carry" of the cyclic
cocycle with a group homomorphism taking a generator to a power.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.NUV2.ChebAux.Transfer

/-! ## The composite `resToGal ∘ inflation`

The composite of the level inflation `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)` with the restriction
`H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)` is the map induced by the composite restriction
`rhoRestrict : Gal(E/M) →* Gal(L/K)` and the coefficient map `Lˣ → Eˣ`. -/

private lemma inflation_comp_resToGal {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L] :
    (groupCohomology.map (NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E))
        (NK.NUV2.ARL.HR.unitsInclRep (K := K) (L := L) (E := E)) 2 :
      groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
        groupCohomology (NK.HassePrinciple.unitsRep K E) 2) ≫
      (groupCohomology.map (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
        (𝟙 (Rep.res (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
          (NK.HassePrinciple.unitsRep K E))) 2 :
      groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
        groupCohomology (NK.HassePrinciple.unitsRep M E) 2) =
    groupCohomology.map (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2 := by
  rw [← groupCohomology.map_comp (NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E))
        (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
        (NK.NUV2.ARL.HR.unitsInclRep (K := K) (L := L) (E := E))
        (𝟙 (Rep.res (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
          (NK.HassePrinciple.unitsRep K E))) 2]
  congr 1

private lemma resToGal_inflation_apply {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L]
    (c : groupCohomology (NK.HassePrinciple.unitsRep K L) 2) :
    (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom
        ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom c)
      = (groupCohomology.map (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E))
          (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2).hom c := by
  have h1 : (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom
      ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom c)
      = ((groupCohomology.map (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
          (𝟙 (Rep.res (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
            (NK.HassePrinciple.unitsRep K E))) 2 :
          groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
            groupCohomology (NK.HassePrinciple.unitsRep M E) 2)).hom
        ((groupCohomology.map (NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E))
          (NK.NUV2.ARL.HR.unitsInclRep (K := K) (L := L) (E := E)) 2 :
          groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
            groupCohomology (NK.HassePrinciple.unitsRep K E) 2).hom c) := rfl
  rw [h1, ← ConcreteCategory.comp_apply]
  rw [← groupCohomology.map_comp (NK.NUV2.ARL.HR.restrictHom (K := K) (L := L) (E := E))
      (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
      (NK.NUV2.ARL.HR.unitsInclRep (K := K) (L := L) (E := E))
      (𝟙 (Rep.res (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E))
        (NK.HassePrinciple.unitsRep K E))) 2]
  congr 1

/-! ## The coefficient map on the image of a global element -/

private lemma unitsInclRepM_unitsImage {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L] (x : Kˣ) :
    (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom
        (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
          (Units.map (algebraMap K M).toMonoidHom x) := by
  show Additive.ofMul (Units.map (algebraMap L E).toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom x))
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x))
  congr 1
  ext
  simp only [Units.coe_map]
  exact (IsScalarTower.algebraMap_apply K L E (x : K)).symm.trans
    (IsScalarTower.algebraMap_apply K M E (x : K))

/-! ## The generator of `Gal(E/M)` adapted to `g` -/

private lemma rhoRestrict_injective {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) :
    Function.Injective (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E)) := by
  intro σ τ h
  have hL : ∀ y : L, σ (algebraMap L E y) = τ (algebraMap L E y) := by
    intro y
    rw [← NK.NUV2.ARL.HR.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ y,
        ← NK.NUV2.ARL.HR.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) τ y, h]
  have hAlg : (σ.restrictScalars K).toAlgHom = (τ.restrictScalars K).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    intro x hx
    rcases hx with ⟨y, hy⟩ | ⟨m, hm⟩
    · rw [← hy]; exact hL y
    · rw [← hm]; simp
  exact AlgEquiv.ext fun x => AlgHom.congr_fun hAlg x

/-- **The generator of `Gal(E/M)` adapted to the generator `g` of `Gal(L/K)`.**

If `E = L·M` and `Gal(L/K)` is cyclic generated by `g`, then `Gal(E/M)` is cyclic, and among its
generators there is one with `rhoRestrict g' = g ^ m` where `m · |Gal(E/M)| = |Gal(L/K)|`
(namely `m = [L ⊓ M : K]`, the index of the image of the restriction). -/
private lemma exists_generator_rhoRestrict {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L]
    [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E]
    [IsScalarTower K M E] [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E] [IsGalois M E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) :
    ∃ (g' : E ≃ₐ[M] E) (hg' : ∀ σ : E ≃ₐ[M] E, σ ∈ Subgroup.zpowers g') (m : ℕ),
      NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E) g' = g ^ m ∧
      m * Fintype.card (E ≃ₐ[M] E) = Fintype.card (L ≃ₐ[K] L) := by
  have hinj : Function.Injective
      (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E)) :=
    rhoRestrict_injective (K := K) (L := L) (M := M) (E := E) hgen
  have hcyc : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, eq_top_iff.mpr fun x _ => hg x⟩
  haveI := hcyc
  obtain ⟨m, hmH, hmcard⟩ := NK.CFTLib.IdeleHasse.Crux.exists_zpowers_pow_eq_of_isCyclic
    g hg (MonoidHom.range (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E)))
  have hgm : g ^ m ∈ MonoidHom.range
      (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E)) := by
    rw [hmH]; exact Subgroup.mem_zpowers _
  obtain ⟨g', hg'm⟩ := MonoidHom.mem_range.mp hgm
  refine ⟨g', ?_, m, hg'm, ?_⟩
  · intro σ
    have hmem : NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ
        ∈ Subgroup.zpowers
            (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E) g') := by
      rw [hg'm, ← hmH]
      exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hinj (by rw [map_zpow, hk])⟩
  · have hHeq : Nat.card (E ≃ₐ[M] E) = Nat.card ↥(Subgroup.map
        (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E)) ⊤) :=
      (Nat.card_congr Subgroup.topEquiv.toEquiv).symm.trans
        (Subgroup.card_map_of_injective hinj).symm
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← hmcard,
      MonoidHom.range_eq_map, hHeq]

/-! ## The translation -/

theorem cycClassOf_translation {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L]
    [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E]
    [IsScalarTower K M E] [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E] [IsGalois M E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) (x : Kˣ) :
    ∃ (g' : E ≃ₐ[M] E) (hg' : ∀ σ : E ≃ₐ[M] E, σ ∈ Subgroup.zpowers g'),
      (NK.NUV2.ChebAux.Transfer.resToGal K M E).hom
          ((NK.NUV2.ARL.HR.inflation (K := K) (L := L) (E := E)).hom
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x))
        = NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := M) (F := E) g' hg'
            (Units.map (algebraMap K M).toMonoidHom x) := by
  obtain ⟨g', hg', m, hg'm, hcard⟩ :=
    exists_generator_rhoRestrict (K := K) (L := L) (M := M) (E := E) hgen g hg
  refine ⟨g', hg', ?_⟩
  have hfree : ∀ σ : L ≃ₐ[K] L,
      (NK.HassePrinciple.unitsRep K L).ρ σ
        (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x :=
    fun σ => NK.CFTLib.IdeleHasse.Descent.unitsRep_apply_unitsImage (K := K) (F := L) σ x
  have hfreeM : ∀ σ : E ≃ₐ[M] E,
      (NK.HassePrinciple.unitsRep M E).ρ σ
        (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
          (Units.map (algebraMap K M).toMonoidHom x))
      = NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
          (Units.map (algebraMap K M).toMonoidHom x) :=
    fun σ => NK.CFTLib.IdeleHasse.Descent.unitsRep_apply_unitsImage (K := M) (F := E) σ
      (Units.map (algebraMap K M).toMonoidHom x)
  have ha' : (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom
        (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x)
      = NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
          (Units.map (algebraMap K M).toMonoidHom x) :=
    unitsInclRepM_unitsImage (K := K) (L := L) (M := M) (E := E) x
  rw [resToGal_inflation_apply (K := K) (L := L) (M := M) (E := E)
    (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)]
  rw [show NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x
      = NK.CFTLib.Descent.cycClass (NK.HassePrinciple.unitsRep K L) g hg
          (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x) hfree from rfl]
  rw [NK.CFTLib.IdeleHasse.Descent.map_cycClass (NK.HassePrinciple.unitsRep K L)
      (NK.HassePrinciple.unitsRep M E)
      (NK.NUV2.ARL.HR.rhoRestrict (K := K) (L := L) (M := M) (E := E))
      g hg g' hg' m hg'm hcard
      (NK.NUV2.ARL.HR.unitsInclRepM (K := K) (L := L) (M := M) (E := E))
      (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x) hfree
      (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
        (Units.map (algebraMap K M).toMonoidHom x)) ha' hfreeM]
  rfl

end NK.NUV2.ChebAux.Transfer
