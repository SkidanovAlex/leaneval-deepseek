import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Canonical seam for the complex place, `p = 2` (lead design archp2_1008, revision 2)

COPY-READY: install verbatim as `Submission/Work/SSGRoute/ArchDictionary/archSeamDefs2.lean`.
It imports and does NOT change `archSeamDefs`.

Defect fixed (H4923, `seamUnits_equivariant` declared MIS-STATED): `ArchSeamP2.seamUnits` spells
`K_w ≃+* ℂ` by `Classical.choose` of an `∃` that pins the spelling only on `K`, so it is
`d`-equivariant only on `μ₂`.  `Φ` itself is unaffected: `seamCoeffLoc` only ever evaluates
`seamUnits` on `μ₂` (`E'` is 2-torsion), where every spelling agrees, so `seamCoeffLoc`,
`archPhiOf` and the proved D5/D6/D8 stand.  The only consumer of full equivariance is the PROOF of
`archPhiSeam_square` (D2, step 5–6: the lift `ã := ũ ∘ n ∘ τ₂`).  It must use the canonical seam
below instead of `seamUnits`:

* `seamSpell φ hne : K_w ≃+* ℂ` — `E := ringEquivComplexOfIsComplex` if the place's embedding is
  `φ|_K`, else `conj ∘ E` (`embedding_mk_eq`); no choice;
* `seamUnitsCan` — `Units.map (seamSpell.symm ∘ φ)`;
* `seamUnitsCan_on_K` (extends the completion map `Kˣ → K_wˣ`), `seamUnitsCan_equivariant`
  (`d`-equivariant on ALL of `Ωˣ`), `seamUnitsCan_neg_one`, `seamUnits_neg_one'`,
  `seamUnitsCan_eq_seamUnits_of_mul_self` (the two seams agree on `μ₂`) — all PROVED.

Stated at `w = seamPlace φ`; at a general `w` use `subst hw` (`seamPlace φ` is the reducible
`Place.ofInfinite (mk (φ.comp (algebraMap K Ω)))`).  The three transport lemmas are H4923's
(`ArchDictionary/seamUnits_equivariant.lean`), copied under a new namespace so that the module
with the false-stated `seamUnits_equivariant` is never imported.
-/

namespace Work.SSGRoute.ArchDictionary.ArchSeamP2b

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

theorem levelConj_linked (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (d : ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (hd : (d : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c) :
    ∀ y : ↥K, (iPlace (K := K) φ).embedding ((d : ↥K ≃ₐ[k] ↥K) y)
      = starRingEnd ℂ ((iPlace (K := K) φ).embedding y) := by
  rcases NumberField.InfinitePlace.embedding_mk_eq (φ.comp (algebraMap ↥K Ω)) with h | h
  · refine Work.SSGRoute.E1aClean.seamLevelConj K (iPlace (K := K) φ) d c hd.symm φ ?_ hlink
    intro y
    rw [show (iPlace (K := K) φ).embedding = φ.comp (algebraMap ↥K Ω) from h]
    rfl
  · refine Work.SSGRoute.E1aClean.seamLevelConj K (iPlace (K := K) φ) d c hd.symm
      (NumberField.ComplexEmbedding.conjugate φ) ?_ ?_
    · intro y
      rw [show (iPlace (K := K) φ).embedding
        = NumberField.ComplexEmbedding.conjugate (φ.comp (algebraMap ↥K Ω)) from h]
      rfl
    · intro x
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
      rw [hlink x]

/-- **The local action of `d` is complex conjugation, in the canonical spelling.**  This is
`Work.sha2_hasse.localAutHom_ringEquivComplex` fed with `levelConj_linked`. -/
theorem localAutHom_conj_transport (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (d : ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (hd : (d : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c) :
    ∀ y : NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ),
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne)
          (NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (seamPlace (K := K) φ) d y)
        = starRingEnd ℂ
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot
              (k := k) (K := ↥K) hne) y) :=
  Work.sha2_hasse.localAutHom_ringEquivComplex (K := k) (L := ↥K) (iPlace (K := K) φ)
    (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne)
    d (levelConj_linked c φ hlink d hd)

/-- **The precise gap of the requested statement.**  For an *arbitrary* spelling
`e : K_w ≃+* ℂ` of the completion at the place of `φ`, the identity `e.symm ∘ φ` is `d`-equivariant
at `u` if and only if the transported spelling `δ := E ∘ e.symm` commutes with complex conjugation
at `φ u`:

    E (e.symm (conj (φ u))) = conj (E (e.symm (φ u))).

The specification `e ∘ algebraMap = φ ∘ algebraMap` (which is all that the `∃` of
`unitsToLocalUnitsHom_eq_embedding` — hence `Classical.choose`, hence `seamUnits` — provides)
constrains `e` only on the proper subfield `K ⊆ K_w` and does not imply this. -/
theorem seamUnits_spelling_iff (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (d : ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (hd : (d : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c)
    (e : NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ) ≃+* ℂ) (u : Ωˣ) :
    (Units.map ((e.symm.toRingHom.comp φ).toMonoidHom) (Work.SSGRoute.algEquivUnitsMapΩ k Ω c u)
        = NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) (seamPlace (K := K) φ) d
            (Units.map ((e.symm.toRingHom.comp φ).toMonoidHom) u))
      ↔ (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne)
            (e.symm (starRingEnd ℂ (φ (u : Ω))))
          = starRingEnd ℂ
              (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
                (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot
                  (k := k) (K := ↥K) hne) (e.symm (φ (u : Ω))))) := by
  have htrans := localAutHom_conj_transport c φ hlink hne d hd
  have hunits :
      (Units.map ((e.symm.toRingHom.comp φ).toMonoidHom) (Work.SSGRoute.algEquivUnitsMapΩ k Ω c u)
          = NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) (seamPlace (K := K) φ) d
              (Units.map ((e.symm.toRingHom.comp φ).toMonoidHom) u))
        ↔ e.symm (φ (c (u : Ω))) = NK.HassePrinciple.localAutHom (K := k) (L := ↥K)
              (seamPlace (K := K) φ) d (e.symm (φ (u : Ω))) := by
    rw [Units.ext_iff, Units.coe_map, Work.SSGRoute.algEquivUnitsMapΩ_coe,
      NK.HassePrinciple.coe_localUnitsEquiv, Units.coe_map]
    exact Iff.rfl
  rw [hunits, hlink u]
  have hE : Function.Injective
      (fun z : NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ) =>
        NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot
            (k := k) (K := ↥K) hne) z) :=
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot
        (k := k) (K := ↥K) hne)).injective
  rw [← hE.eq_iff, htrans (e.symm (φ (u : Ω)))]

/-- The canonical spelling of `K_w ≃+* ℂ` at the seam place: no choice. -/
noncomputable def seamSpell (φ : Ω →+* ℂ)
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) :
    NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ) ≃+* ℂ := by
  classical
  exact if (iPlace (K := K) φ).embedding = φ.comp (algebraMap ↥K Ω) then
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne)
    else
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne)).trans
        Complex.conjAe.toRingEquiv

/-- **The canonical seam on units.** -/
noncomputable def seamUnitsCan (φ : Ω →+* ℂ)
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) :
    Ωˣ →* (NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ))ˣ :=
  Units.map (((seamSpell (K := K) φ hne).symm.toRingHom.comp φ).toMonoidHom)

theorem seamUnitsCan_coe (φ : Ω →+* ℂ)
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) (u : Ωˣ) :
    ((seamUnitsCan (K := K) φ hne u : (NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ))ˣ) :
      NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ))
      = (seamSpell (K := K) φ hne).symm (φ (u : Ω)) := rfl

/-- **`d`-equivariance on all of `Ωˣ`** (PROVED). -/
theorem seamUnitsCan_equivariant (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (d : ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (hd : (d : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c) (u : Ωˣ) :
    seamUnitsCan (K := K) φ hne (Work.SSGRoute.algEquivUnitsMapΩ k Ω c u)
      = NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) (seamPlace (K := K) φ) d
          (seamUnitsCan (K := K) φ hne u) := by
  show Units.map ((((seamSpell (K := K) φ hne).symm.toRingHom.comp φ).toMonoidHom))
      (Work.SSGRoute.algEquivUnitsMapΩ k Ω c u)
    = NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) (seamPlace (K := K) φ) d
        (Units.map ((((seamSpell (K := K) φ hne).symm.toRingHom.comp φ).toMonoidHom)) u)
  rw [seamUnits_spelling_iff c φ hlink hne d hd (seamSpell (K := K) φ hne) u]
  unfold seamSpell
  split_ifs with h
  · rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  · simp only [RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply]
    simp [Complex.conjAe]

/-- **`seamUnitsCan` extends the completion map `Kˣ → K_wˣ`** (PROVED). -/
theorem seamUnitsCan_on_K (φ : Ω →+* ℂ)
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) (x : (↥K)ˣ) :
    seamUnitsCan (K := K) φ hne (Units.map (algebraMap ↥K Ω).toMonoidHom x)
      = NK.HassePrinciple.unitsToLocalUnitsHom (seamPlace (K := K) φ) x := by
  classical
  have hvC := Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne
  have hcoe : ∀ y : ↥K,
      NumberField.InfinitePlace.Completion.extensionEmbedding (iPlace (K := K) φ)
        (algebraMap ↥K (iPlace (K := K) φ).Completion y) = (iPlace (K := K) φ).embedding y := by
    intro y
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  have key : (seamSpell (K := K) φ hne)
      (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ)) (x : ↥K))
      = φ (algebraMap ↥K Ω (x : ↥K)) := by
    unfold seamSpell
    split_ifs with h
    · rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, hcoe, h]
      rfl
    · have h2 : (iPlace (K := K) φ).embedding
          = NumberField.ComplexEmbedding.conjugate (φ.comp (algebraMap ↥K Ω)) :=
        (NumberField.InfinitePlace.embedding_mk_eq (φ.comp (algebraMap ↥K Ω))).resolve_left h
      rw [RingEquiv.trans_apply, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
        hcoe, h2]
      simp [NumberField.ComplexEmbedding.conjugate, Complex.conjAe]
  apply Units.ext
  rw [seamUnitsCan_coe]
  show (seamSpell (K := K) φ hne).symm (φ (algebraMap ↥K Ω (x : ↥K)))
    = algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (seamPlace (K := K) φ)) (x : ↥K)
  rw [← key, RingEquiv.symm_apply_apply]

theorem seamUnitsCan_neg_one (φ : Ω →+* ℂ)
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) :
    seamUnitsCan (K := K) φ hne (-1) = -1 := by
  apply Units.ext
  rw [seamUnitsCan_coe]
  simp

theorem seamUnits_neg_one' (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) :
    seamUnits c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne (-1) = -1 := by
  apply Units.ext
  simp [seamUnits]

/-- **The two seams agree on `μ₂`**, so `seamCoeffLoc` (built on `seamUnits`) equals the
canonical push on every 2-torsion value (PROVED). -/
theorem seamUnitsCan_eq_seamUnits_of_mul_self (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) (u : Ωˣ) (hu : u * u = 1) :
    seamUnitsCan (K := K) φ hne u = seamUnits c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne u := by
  have h : (u : Ω) * (u : Ω) = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · rw [show u = 1 from Units.ext h1, map_one, map_one]
  · rw [show u = -1 from Units.ext h1, seamUnitsCan_neg_one, seamUnits_neg_one']

#print axioms seamUnitsCan_equivariant
#print axioms seamUnitsCan_on_K
#print axioms seamUnitsCan_eq_seamUnits_of_mul_self

end Work.SSGRoute.ArchDictionary.ArchSeamP2b
