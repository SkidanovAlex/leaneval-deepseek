import Mathlib
import Submission.NK.CFTLib.HRclean.ARLClean
import Submission.NK.CFTLib.IdeleHasse.Descent.transferCore
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Crux.zpowersSubgroup
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

/-!
# CLEAN COPY (agent H-): the `NK.NUV2.ChebAux.Transfer` toolkit for the Brauer transfer

Concatenation of `Submission/Work/NUV2/ChebAux/Transfer/Defs.lean` (the restriction `resToGal`),
`.../cycClassOf_translation.lean` (the translation identity T1) and
`.../locUnits_res_inflation_eq_zero.lean` (the localisation of the level inflation, T2), with the
imports of `.../Defs.lean` and of `NK.CFTLib.HRclean.ARL.TransferSupport` redirected to the clean copies
in this directory (see `Submission/Work/CFTLib/HRclean/README.md` for the import-cycle that
motivates them).  All statements and proofs are unchanged.
-/

namespace NK.CFTLib.HRclean.Cheb


/-- **The restriction `H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)`** along the inclusion of the subgroup
`Gal(E/M) ↪ Gal(E/K)`. -/
noncomputable def resToGal (K M E : Type) [Field K] [Field M] [Field E] [Algebra K M]
    [Algebra K E] [Algebra M E] [IsScalarTower K M E] :
    groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
      groupCohomology (NK.HassePrinciple.unitsRep M E) 2 :=
  (groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt
    (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E)) 2).app
      (NK.HassePrinciple.unitsRep K E)



/-! ## The composite `resToGal ∘ inflation`

The composite of the level inflation `H²(Gal(L/K), Lˣ) → H²(Gal(E/K), Eˣ)` with the restriction
`H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)` is the map induced by the composite restriction
`rhoRestrict : Gal(E/M) →* Gal(L/K)` and the coefficient map `Lˣ → Eˣ`. -/

private lemma inflation_comp_resToGal {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L] :
    (groupCohomology.map (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E)) 2 :
      groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
        groupCohomology (NK.HassePrinciple.unitsRep K E) 2) ≫
      (groupCohomology.map (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
        (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
          (NK.HassePrinciple.unitsRep K E))) 2 :
      groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
        groupCohomology (NK.HassePrinciple.unitsRep M E) 2) =
    groupCohomology.map (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2 := by
  rw [← groupCohomology.map_comp (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
        (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E))
        (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
          (NK.HassePrinciple.unitsRep K E))) 2]
  congr 1

private lemma resToGal_inflation_apply {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L]
    (c : groupCohomology (NK.HassePrinciple.unitsRep K L) 2) :
    (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom c)
      = (groupCohomology.map (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
          (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2).hom c := by
  have h1 : (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
      ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom c)
      = ((groupCohomology.map (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
          (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
            (NK.HassePrinciple.unitsRep K E))) 2 :
          groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
            groupCohomology (NK.HassePrinciple.unitsRep M E) 2)).hom
        ((groupCohomology.map (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
          (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E)) 2 :
          groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
            groupCohomology (NK.HassePrinciple.unitsRep K E) 2).hom c) := rfl
  rw [h1, ← ConcreteCategory.comp_apply]
  rw [← groupCohomology.map_comp (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
      (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
      (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E))
      (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
        (NK.HassePrinciple.unitsRep K E))) 2]
  congr 1

/-! ## The coefficient map on the image of a global element -/

private lemma unitsInclRepM_unitsImage {K L M E : Type} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E] [IsGalois K L] (x : Kˣ) :
    (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom
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
    Function.Injective (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)) := by
  intro σ τ h
  have hL : ∀ y : L, σ (algebraMap L E y) = τ (algebraMap L E y) := by
    intro y
    rw [← NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ y,
        ← NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) τ y, h]
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
      NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) g' = g ^ m ∧
      m * Fintype.card (E ≃ₐ[M] E) = Fintype.card (L ≃ₐ[K] L) := by
  have hinj : Function.Injective
      (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)) :=
    rhoRestrict_injective (K := K) (L := L) (M := M) (E := E) hgen
  have hcyc : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, eq_top_iff.mpr fun x _ => hg x⟩
  haveI := hcyc
  obtain ⟨m, hmH, hmcard⟩ := NK.CFTLib.IdeleHasse.Crux.exists_zpowers_pow_eq_of_isCyclic
    g hg (MonoidHom.range (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)))
  have hgm : g ^ m ∈ MonoidHom.range
      (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)) := by
    rw [hmH]; exact Subgroup.mem_zpowers _
  obtain ⟨g', hg'm⟩ := MonoidHom.mem_range.mp hgm
  refine ⟨g', ?_, m, hg'm, ?_⟩
  · intro σ
    have hmem : NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ
        ∈ Subgroup.zpowers
            (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) g') := by
      rw [hg'm, ← hmH]
      exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hinj (by rw [map_zpow, hk])⟩
  · have hHeq : Nat.card (E ≃ₐ[M] E) = Nat.card ↥(Subgroup.map
        (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)) ⊤) :=
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
      (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
          ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
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
  have ha' : (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom
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
      (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
      g hg g' hg' m hg'm hcard
      (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E))
      (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := L) x) hfree
      (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := M) (F := E)
        (Units.map (algebraMap K M).toMonoidHom x)) ha' hfreeM]
  rfl



section General

variable {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
  [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
  [IsGalois K L] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-- The restriction map `Gal(E/M) →* Gal(L/K)` carries the stabiliser of a place `ŵ` of `E` into
the stabiliser of the place `v'` of `L` below it. -/
theorem rhoRestrict_smul_eq_of_fixes (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') (σ : E ≃ₐ[M] E) (hσ : σ • ŵ = ŵ) :
    (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ) • v' = v' := by
  have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := L) (L := E)
      (τ := σ.restrictScalars K)
      (A := NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ)
      (fun y => NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ y) hv
  rw [show (σ.restrictScalars K) • ŵ = ŵ from hσ] at h1
  exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 hv

/-- The induced map of stabilisers `Γ_ŵ^{E/M} →* Γ_{v'}^{L/K}`. -/
noncomputable def stabilizerMapRho (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    MulAction.stabilizer (E ≃ₐ[M] E) ŵ →* MulAction.stabilizer (L ≃ₐ[K] L) v' where
  toFun σ := ⟨NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1, by
    rw [MulAction.mem_stabilizer_iff]
    exact rhoRestrict_smul_eq_of_fixes ŵ v' hv σ.1 (MulAction.mem_stabilizer_iff.mp σ.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.1 τ.1)

theorem stabilizerMapRho_subtype (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype.comp (stabilizerMapRho ŵ v' hv) =
      (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)).comp
        (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype :=
  MonoidHom.ext fun σ => rfl

/-- Cast of the local algebra map along a change of the place upstairs. -/
lemma localAlgebraMapUnits_cast_up {a a' : NK.GlobalCFT.Place E} {b b' : NK.GlobalCFT.Place L}
    (h1 : a = a') (h2 : b = b') (Ha : NK.GlobalCFT.Place.LiesOver a b)
    (H : NK.GlobalCFT.Place.LiesOver a' b') (x : (NK.GlobalCFT.Place.localField L b)ˣ) :
    h1 ▸ (NK.GlobalCFT.Place.localAlgebraMapUnits a b Ha x)
      = NK.GlobalCFT.Place.localAlgebraMapUnits a' b' H (h2 ▸ x) := by
  cases h1
  exact NK.HassePrinciple.localAlgebraMapUnits_cast a h2 Ha H x

/-- The local algebra map along a restriction of scalars. -/
lemma localRingEquiv_localAlgebraMapUnits_of_restrict' (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (σ : E ≃ₐ[M] E) (A : L ≃ₐ[K] L)
    (hA : ∀ y : L, algebraMap L E (A y) = σ (algebraMap L E y))
    {h : NK.GlobalCFT.Place.LiesOver ŵ v'}
    {h' : NK.GlobalCFT.Place.LiesOver (σ • ŵ) (A • v')}
    (a : (NK.GlobalCFT.Place.localField L v')ˣ) :
    Units.map (NK.GlobalCFT.Place.localRingEquiv σ ŵ).toMonoidHom
        (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' h a) =
      NK.GlobalCFT.Place.localAlgebraMapUnits (σ • ŵ) (A • v') h'
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v').toMonoidHom a) :=
  NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict (K := K) (F := L) (L := E)
    (τ := σ.restrictScalars K) A hA h h' a

/-- The local coefficient morphism `L_{v'}ˣ → E_ŵˣ` along the restriction
`Γ_ŵ^{E/M} →* Γ_{v'}^{L/K}`. -/
noncomputable def localUnitsMapRhoCoeff (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    Rep.res (stabilizerMapRho ŵ v' hv) (NK.HassePrinciple.localUnitsRep K L v') ⟶
      NK.HassePrinciple.localUnitsRep M E ŵ :=
  Rep.ofHom
    { toFun := ⇑(NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive
      map_add' := fun x y =>
        map_add (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv
              (NK.HassePrinciple.localUnitsEquiv v'
                (stabilizerMapRho ŵ v' hv σ) (Additive.toMul x)))
            = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv ŵ σ
              (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv (Additive.toMul x)))
        congr 1
        set u : (NK.GlobalCFT.Place.localField L v')ˣ := Additive.toMul x with hu
        have hσ : σ.1 • ŵ = ŵ := MulAction.mem_stabilizer_iff.mp σ.2
        have hA : (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) • v' = v' :=
          rhoRestrict_smul_eq_of_fixes ŵ v' hv σ.1 hσ
        have hcoe : ∀ y : L, algebraMap L E
            ((NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) y)
            = σ.1 (algebraMap L E y) :=
          fun y => NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ.1 y
        have h' : NK.GlobalCFT.Place.LiesOver ((σ.1.restrictScalars K) • ŵ)
            ((NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) • v') :=
          NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := L) (L := E)
            (τ := σ.1.restrictScalars K)
            (A := NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1)
            hcoe hv
        have key := localRingEquiv_localAlgebraMapUnits_of_restrict' (K := K) (L := L) (M := M)
          (E := E) ŵ v' σ.1
          (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) hcoe
          (h := hv) (h' := h') u
        rw [show stabilizerMapRho ŵ v' hv σ =
            (⟨NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1, hA⟩ :
              MulAction.stabilizer (L ≃ₐ[K] L) v') from Subtype.ext rfl]
        rw [NK.NUV2.LC.RouteB.localUnitsEquiv_eq_cast (F := K) (L := L),
          NK.NUV2.LC.RouteB.localUnitsEquiv_eq_cast (F := M) (L := E)]
        rw [key]
        exact (localAlgebraMapUnits_cast_up
          (a := σ.1 • ŵ) (a' := ŵ) (b := (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M)
            (E := E) σ.1) • v') (b' := v') hσ hA h' hv
          (Units.map (NK.GlobalCFT.Place.localRingEquiv
            (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) v').toMonoidHom
            u)).symm }

/-- The local level map `H²(Γ_{v'}^{L/K}, L_{v'}ˣ) → H²(Γ_ŵ^{E/M}, E_ŵˣ)`. -/
noncomputable def localLevelMapRho (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    groupCohomology (NK.HassePrinciple.localUnitsRep K L v') 2 ⟶
      groupCohomology (NK.HassePrinciple.localUnitsRep M E ŵ) 2 :=
  groupCohomology.map (stabilizerMapRho ŵ v' hv)
      (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv) (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
      (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2

/-! ### The changes of level

We record the value of the two natural coefficient morphisms on elements of `Additive _`, which is
what the elementwise comparison of morphisms of representations reduces to. -/

@[simp] theorem unitsInclRepM_hom_ofMul (u : Lˣ) :
    (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap L E).toMonoidHom u) := rfl

@[simp] theorem localUnitsMapRhoCoeff_hom_ofMul (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (hv : NK.GlobalCFT.Place.LiesOver ŵ v')
    (x : (NK.GlobalCFT.Place.localField L v')ˣ) :
    (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv).hom (Additive.ofMul x)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv x) := rfl

/-- Naturality of the localisation on `L` in the coefficient morphism of the tower. -/
theorem localLevelMapRho_naturality_aux (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) v'))
        (NK.HassePrinciple.unitsToLocalUnits K L v') 2 ≫
      (groupCohomology.map (stabilizerMapRho ŵ v' hv)
          (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv)
            (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2)
      = groupCohomology.map (stabilizerMapRho ŵ v' hv)
          ((Rep.resFunctor (stabilizerMapRho ŵ v' hv)).map
              (NK.HassePrinciple.unitsToLocalUnits K L v') ≫
            localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2 := by
  rw [← Category.assoc]
  rw [← NK.NUV2.LC.RouteB.map_resFunctor_map (stabilizerMapRho ŵ v' hv)
    (NK.HassePrinciple.unitsToLocalUnits K L v') 2]
  rw [← NK.NUV2.LC.RouteB.map_f_comp_id (stabilizerMapRho ŵ v' hv)
    ((Rep.resFunctor (stabilizerMapRho ŵ v' hv)).map
      (NK.HassePrinciple.unitsToLocalUnits K L v'))
    (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2]

/-- **The square of level change.**  The composite
`H²(Gal(L/K), Lˣ) → H²(Gal(E/M), Eˣ) → H²(Γ_ŵ^{E/M}, E_ŵˣ)` (inflation along `L ⊆ E` followed by
restriction along `Gal(E/M) ⊆ Gal(E/K)` and localisation) equals the localisation at the place
`v'` below `ŵ` followed by the local level map `localLevelMapRho`. -/
theorem locUnits_rhoRestrict_unitsInclRepM_eq (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    (groupCohomology.map (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2) ≫
      (NK.HassePrinciple.locUnits M E ŵ)
      = (NK.HassePrinciple.locUnits K L v') ≫
        (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv) := by
  rw [show (NK.HassePrinciple.locUnits M E ŵ) =
        (groupCohomology.map (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype
            (NK.HassePrinciple.unitsRep M E))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (NK.HassePrinciple.unitsToLocalUnits M E ŵ) 2) from rfl,
      show (NK.HassePrinciple.locUnits K L v') =
        (groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype
            (NK.HassePrinciple.unitsRep K L))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) v'))
          (NK.HassePrinciple.unitsToLocalUnits K L v') 2) from rfl]
  rw [show (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv) =
        (groupCohomology.map (stabilizerMapRho ŵ v' hv)
          (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv)
            (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2) from rfl]
  conv_lhs => rw [NK.NUV2.LC.RouteB.map_id_comp_apply, ← groupCohomology.map_comp]
  conv_rhs => rw [Category.assoc]
  conv_rhs => rw [localLevelMapRho_naturality_aux (K := K) (L := L) (M := M) (E := E) ŵ v' hv]
  conv_rhs => rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr
    (G := MulAction.stabilizer (E ≃ₐ[M] E) ŵ) (H := L ≃ₐ[K] L)
    (A := NK.HassePrinciple.unitsRep K L)
    (B := NK.HassePrinciple.localUnitsRep M E ŵ)
    (f := (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)).comp
      (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype)
    (g := (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype.comp (stabilizerMapRho ŵ v' hv))
    (stabilizerMapRho_subtype ŵ v' hv).symm ?_ 2
  ext x
  conv_lhs => rw [← ofMul_toMul x]
  conv_rhs => rw [← ofMul_toMul x]
  simp only [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, LinearMap.comp_apply,
    LinearMap.id_apply, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.id_apply,
    NK.HassePrinciple.unitsToLocalUnits_apply, unitsInclRepM_hom_ofMul,
    localUnitsMapRhoCoeff_hom_ofMul]
  exact (NK.NUV2.LC.RouteB.localAlgebraMapUnits_algebraMap_units (L := L) (M := E) hv
    (Additive.toMul x)).symm

/-- The composite `inflation ≫ resToGal` in the `unitsRep`-vocabulary. -/
theorem resToGal_inflation_eq_map :
    ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)) ≫
        (NK.CFTLib.HRclean.Cheb.resToGal K M E)) =
      groupCohomology.map (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2 := by
  have h1 : (NK.CFTLib.HRclean.Cheb.resToGal K M E) =
      (groupCohomology.map (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
        (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
          (NK.HassePrinciple.unitsRep K E))) 2 :
        groupCohomology (NK.HassePrinciple.unitsRep K E) 2 ⟶
          groupCohomology (NK.HassePrinciple.unitsRep M E) 2) := rfl
  have h2 : (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)) =
      (groupCohomology.map (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E)) 2 :
        groupCohomology (NK.HassePrinciple.unitsRep K L) 2 ⟶
          groupCohomology (NK.HassePrinciple.unitsRep K E) 2) := rfl
  rw [h1, h2, ← groupCohomology.map_comp
    (NK.CFTLib.HRclean.ARL.restrictHom (K := K) (L := L) (E := E))
    (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
    (NK.CFTLib.HRclean.ARL.unitsInclRep (K := K) (L := L) (E := E))
    (𝟙 (Rep.res (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E))
      (NK.HassePrinciple.unitsRep K E))) 2]
  congr 1

end General

/-- **Local triviality transfers along `inf` and `res`.**  If the cyclic class of `x` at the level
`L/K` is locally trivial at the place `v'` of `L`, then its image under the level change to `E/M`
(the inflation to the level `E/K` followed by the restriction to `Gal(E/M)`) is locally trivial at
every place `ŵ` of `E` above `v'`. -/
theorem locUnits_res_inflation_eq_zero {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K L]
    [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E] [IsScalarTower K L E]
    [IsScalarTower K M E] [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E] [IsGalois M E]
    (g : L ≃ₐ[K] L) (hg : ∀ σ : L ≃ₐ[K] L, σ ∈ Subgroup.zpowers g) (x : Kˣ)
    (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v')
    (hc : (NK.HassePrinciple.locUnits K L v').hom
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) = 0) :
    (NK.HassePrinciple.locUnits M E ŵ).hom
      ((NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x))) = 0 := by
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  have hcomp := resToGal_inflation_eq_map (K := K) (L := L) (M := M) (E := E)
  have hsq := locUnits_rhoRestrict_unitsInclRepM_eq (K := K) (L := L) (M := M) (E := E) ŵ v' hv
  have key : (NK.HassePrinciple.locUnits M E ŵ).hom
        ((NK.CFTLib.HRclean.Cheb.resToGal K M E).hom
          ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)).hom
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)))
      = (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv).hom
          ((NK.HassePrinciple.locUnits K L v').hom
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)) := by
    have h2 : (((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := L) (E := E)) ≫
          (NK.CFTLib.HRclean.Cheb.resToGal K M E)) ≫
          (NK.HassePrinciple.locUnits M E ŵ)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x)
        = ((NK.HassePrinciple.locUnits K L v') ≫
            (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv)).hom
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := L) g hg x) := by
      rw [hcomp, hsq]
    simpa only [ConcreteCategory.comp_apply] using h2
  rw [key, hc]
  exact map_zero _


end NK.CFTLib.HRclean.Cheb
