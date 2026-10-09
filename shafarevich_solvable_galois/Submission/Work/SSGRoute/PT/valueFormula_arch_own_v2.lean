import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.PT.vf_transverse
import Submission.Work.SSGRoute.PT.vf_local_compare
import Submission.Work.SSGRoute.PT.vf_bad_finset
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PT.liesOver_linked
import Submission.Work.SSGRoute.PT.wc_orbit_injective
import Submission.Work.SSGRoute.PT.levelPair_unramified_eq_zero
import Submission.Work.SSGRoute.localSumDecomposition
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.E9c.Core
-- import Submission.Work.SSGRoute.E9c.Lift  -- clashes with E9c.Core
import Submission.Work.SSGRoute.E7cOmega.zfun_pairing_extLoc
import Submission.Work.SSGRoute.E7cOmega.mem_orbit_of_liesOver_conj
import Submission.Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design: _lead_design/flags_1730/flags_1730.md §1-2 (ssg_pt_design_1002/flags_1730). Helpers dispatched as separate nodes: SSGRoute/PT/decompK_linked, liesOver_linked, wc_orbit_injective. Import them once their modules exist; do not re-prove them.
Glue: the finite part is glue_realiser_abstract (proved). The archimedean components βc c (β c) are given, so no realiser is needed there. Apply ext_idele_shapiro over a transversal of all places containing R ∪ {wc c}; it exists by wc_orbit_injective + hseam + hCdisj.
Value formula: v4 V (valueFormula_abstract) at level L, with the transversal containing u_c := mk(φc c|_L). liesOver_linked gives u_c | wc c; decompK_linked gives D_{u_c} = ⟨res_L c⟩. Then E7cOmega.extLoc_push_ideleMap with ι = localUnitsMap makes yonedaPair (extLoc u_c Z) (h|_{D_{u_c}}) literally levelPair (decompKRestrict) (localUnitsMap) (extLoc (wc c) X) (h|_{D_{u_c}}), by unfolding; the glue gives extLoc (wc c) X = βc c (β c).
Do NOT set maxHeartbeats 0; wrap every lake build in timeout.
-/


/-! `valueFormula_arch_own_v2` — copy of `valueFormula_arch_own`
(`Submission/Work/SSGRoute/PT/vf_arch_own.lean`) with the (unused) `hβg_unr` binder removed, all
auxiliary declarations renamed with a `_v2` suffix (so that the module can coexist with the
original).  The proof body is unchanged.  Built by the hub lane for
`finiteS_converse_canonical_v8`. -/

namespace Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped Pointwise
open SSGRoute.PTExt CategoryTheory

section LinkedTransversal

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The archimedean place of a level `L` linked to an embedding `φ : Ω →+* ℂ`**: the place
`mk (φ|_L)`. -/
noncomputable def linkedPlace_v2 (L : IntermediateField k Ω) [NumberField ↥L] (φ : Ω →+* ℂ) :
    NK.GlobalCFT.Place ↥L :=
  NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥L Ω)))

/-- The linked place of `Ω` is archimedean. -/
theorem not_isFinite_linkedPlace_v2 (L : IntermediateField k Ω) [NumberField ↥L] (φ : Ω →+* ℂ) :
    ¬ (linkedPlace_v2 L φ).IsFinite := by
  rw [linkedPlace_v2]
  exact NK.GlobalCFT.Place.not_isFinite_ofInfinite _

/-- **The linked places form a tower**: for `K ≤ L`, the linked place of `L` lies over the linked
place of `K` (`Work.SSGRoute.PT.liesOver_linked`). -/
theorem linkedPlace_liesOver_v2 (K L : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (φ : Ω →+* ℂ) :
    NK.GlobalCFT.Place.LiesOver (linkedPlace_v2 L φ) (linkedPlace_v2 K φ) :=
  liesOver_linked k Ω K L φ

/-- **Distinct members of `C` have non-conjugate linked places.**  Conjugate linked places imply
conjugate involutions (`wc_orbit_injective`) and the members of `C` are pairwise non-conjugate
(`hCdisj`). -/
theorem linkedPlace_orbit_injective_v2
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    (C : Finset (Ω ≃ₐ[k] Ω)) (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hCinv : ∀ c ∈ C, c ^ 2 = 1) (hC1 : ∀ c ∈ C, c ≠ 1)
    (hCprim : ∀ c ∈ C, ∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x))
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    {c c' : Ω ≃ₐ[k] Ω} (hcC : c ∈ C) (hc'C : c' ∈ C)
    (hconj : ∃ σ : ↥L ≃ₐ[k] ↥L, σ • linkedPlace_v2 L (φc c') = linkedPlace_v2 L (φc c)) :
    c = c' := by
  classical
  obtain ⟨σ, hσ⟩ := hconj
  obtain ⟨ρ, hρ⟩ := wc_orbit_injective k Ω L c' c (hCinv c' hc'C) (hC1 c' hc'C)
    (hCinv c hcC) (hC1 c hcC) (φc c') (φc c) (hCprim c' hc'C) (hCprim c hcC) σ hσ
  exact hCdisj c hcC c' hc'C ⟨ρ⁻¹, by rw [hρ]; group⟩

/-- **A transversal of the places of `L` containing prescribed finite and archimedean places.**

Given the transversal data `R` of the finite places of `Ω` (`hRfin`, `hRdisj`, `hRcov`) and a finite
family `(φc c)_{c ∈ C}` of seam embeddings with pairwise non-conjugate involutions, there is a set
`R''` of places of `L` which

* contains `ofFinite (finQW L v hRfin)` for every `v ∈ R`;
* contains `linkedPlace_v2 L (φc c)` for every `c ∈ C`;
* meets every `Gal(L/k)`-orbit of places of `L` in exactly one point;
* has injective restriction `v ↦ ofFinite (finQW L v)`;
* has no finite places other than those below elements of `R`.

Construction: quotient the places of `L` by the orbit relation and use `Quotient.out` as the
canonical section, overriding it on the finitely many classes that contain a prescribed place
(which are pairwise distinct by `finQW_smul_injective` and `linkedPlace_orbit_injective_v2`). -/
theorem exists_transversal_linked_v2
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hCinv : ∀ c ∈ C, c ^ 2 = 1) (hC1 : ∀ c ∈ C, c ≠ 1)
    (hCprim : ∀ c ∈ C, ∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x))
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') :
    ∃ R'' : Set (NK.GlobalCFT.Place ↥L),
      (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
        NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) ∈ R'') ∧
      (∀ c ∈ C, linkedPlace_v2 L (φc c) ∈ R'') ∧
      (∀ w : NK.GlobalCFT.Place ↥L, ∃! w' : R'', ∃ σ : ↥L ≃ₐ[k] ↥L, σ • w = w'.1) ∧
      (∀ (v w : ValuationSubring Ω) (hv : v ∈ R) (hw : w ∈ R),
        NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv)) =
        NK.GlobalCFT.Place.ofFinite (finQW L w (hRfin w hw)) → v = w) ∧
      (∀ w : R'', w.1.IsFinite →
        ∃ (v : ValuationSubring Ω) (hv : v ∈ R),
          w.1 = NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv))) := by
  classical
  let isFinClass : Quotient (placeOrbitSetoid L) → Prop := fun q =>
    ∃ p : {v : ValuationSubring Ω // v ∈ R},
      q = Quotient.mk (placeOrbitSetoid L)
        (NK.GlobalCFT.Place.ofFinite (finQW L p.1 (hRfin p.1 p.2)))
  let isLinkClass : Quotient (placeOrbitSetoid L) → Prop := fun q =>
    ∃ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      q = Quotient.mk (placeOrbitSetoid L) (linkedPlace_v2 L (φc c.1))
  let rep : Quotient (placeOrbitSetoid L) → NK.GlobalCFT.Place ↥L := fun q =>
    if h1 : isFinClass q then
      NK.GlobalCFT.Place.ofFinite (finQW L (Classical.choose h1).1
        (hRfin (Classical.choose h1).1 (Classical.choose h1).2))
    else if h2 : isLinkClass q then linkedPlace_v2 L (φc (Classical.choose h2).1)
    else Quotient.out q
  -- the section property
  have rep_mk : ∀ q : Quotient (placeOrbitSetoid L),
      Quotient.mk (placeOrbitSetoid L) (rep q) = q := by
    intro q
    simp only [rep]
    by_cases h1 : isFinClass q
    · rw [dif_pos h1]
      exact (Classical.choose_spec h1).symm
    · rw [dif_neg h1]
      by_cases h2 : isLinkClass q
      · rw [dif_pos h2]
        exact (Classical.choose_spec h2).symm
      · rw [dif_neg h2]
        exact Quotient.out_eq q
  -- the prescribed finite classes are represented by themselves
  have fin_rep : ∀ p : {v : ValuationSubring Ω // v ∈ R},
      rep (Quotient.mk (placeOrbitSetoid L)
        (NK.GlobalCFT.Place.ofFinite (finQW L p.1 (hRfin p.1 p.2))))
      = NK.GlobalCFT.Place.ofFinite (finQW L p.1 (hRfin p.1 p.2)) := by
    intro p
    have hmem : isFinClass (Quotient.mk (placeOrbitSetoid L)
        (NK.GlobalCFT.Place.ofFinite (finQW L p.1 (hRfin p.1 p.2)))) := ⟨p, rfl⟩
    simp only [rep]
    rw [dif_pos hmem]
    set p' := Classical.choose hmem with hp'
    have hspec := Classical.choose_spec hmem
    obtain ⟨σ, hσ⟩ := Quotient.exact hspec.symm
    have heq : p'.1 = p.1 :=
      finQW_smul_injective L R hRfin hRdisj p'.1 p.1 p'.2 p.2 σ hσ
    exact congrArg (fun q => NK.GlobalCFT.Place.ofFinite q)
      (finQW_congr L heq (hRfin p'.1 p'.2) (hRfin p.1 p.2))
  -- the prescribed linked classes are represented by themselves
  have link_rep : ∀ c ∈ C,
      rep (Quotient.mk (placeOrbitSetoid L) (linkedPlace_v2 L (φc c))) = linkedPlace_v2 L (φc c) := by
    intro c hc
    have hnotfin : ¬ isFinClass (Quotient.mk (placeOrbitSetoid L) (linkedPlace_v2 L (φc c))) := by
      rintro ⟨p, hp⟩
      obtain ⟨σ, hσ⟩ := Quotient.exact hp
      have hinf : (σ • linkedPlace_v2 L (φc c)).IsFinite := by rw [hσ]; simp
      exact not_isFinite_linkedPlace_v2 L (φc c)
        ((isFinite_smul_iff L σ (linkedPlace_v2 L (φc c))).mp hinf)
    have hlink : isLinkClass (Quotient.mk (placeOrbitSetoid L) (linkedPlace_v2 L (φc c))) :=
      ⟨⟨c, hc⟩, rfl⟩
    simp only [rep]
    rw [dif_neg hnotfin, dif_pos hlink]
    set c' := Classical.choose hlink with hc'
    have hspec := Classical.choose_spec hlink
    obtain ⟨σ, hσ⟩ := Quotient.exact hspec
    have heq : c'.1 = c := linkedPlace_orbit_injective_v2 K L C φc hCinv hC1 hCprim hCdisj c'.2 hc
      ⟨σ, hσ⟩
    rw [heq]
  have hbasic : ∀ w : NK.GlobalCFT.Place ↥L,
      ∃ σ : ↥L ≃ₐ[k] ↥L, σ • w = rep (Quotient.mk (placeOrbitSetoid L) w) := by
    intro w
    obtain ⟨σ, hσ⟩ := Quotient.exact (rep_mk (Quotient.mk (placeOrbitSetoid L) w))
    refine ⟨σ⁻¹, ?_⟩
    show σ⁻¹ • w = rep (Quotient.mk (placeOrbitSetoid L) w)
    conv_lhs => rw [← hσ]
    exact inv_smul_smul σ _
  refine ⟨Set.range rep, ?_, ?_, ?_, ?_, ?_⟩
  · rintro v hv
    exact ⟨Quotient.mk (placeOrbitSetoid L)
      (NK.GlobalCFT.Place.ofFinite (finQW L v (hRfin v hv))),
      fin_rep ⟨v, hv⟩⟩
  · intro c hc
    exact ⟨Quotient.mk (placeOrbitSetoid L) (linkedPlace_v2 L (φc c)), link_rep c hc⟩
  · intro w
    refine ⟨⟨rep (Quotient.mk (placeOrbitSetoid L) w),
      ⟨Quotient.mk (placeOrbitSetoid L) w, rfl⟩⟩, hbasic w, ?_⟩
    rintro ⟨y, hy⟩ ⟨τ, hτ⟩
    obtain ⟨q, rfl⟩ := hy
    apply Subtype.ext
    show rep q = rep (Quotient.mk (placeOrbitSetoid L) w)
    have hrel : placeOrbitRel L w (rep q) := ⟨τ, hτ⟩
    have hclass_eq : Quotient.mk (placeOrbitSetoid L) (rep q)
        = Quotient.mk (placeOrbitSetoid L) w := (Quotient.sound hrel).symm
    exact (congrArg rep (rep_mk q)).symm.trans (congrArg rep hclass_eq)
  · intro v w hv hw h
    exact finQW_smul_injective L R hRfin hRdisj v w hv hw 1 (by simpa using h)
  · rintro ⟨y, hy⟩ hfin
    obtain ⟨q, rfl⟩ := hy
    simp only [rep] at hfin ⊢
    split_ifs at hfin ⊢ with h1 h2
    · exact ⟨(Classical.choose h1).1, (Classical.choose h1).2, rfl⟩
    · exact absurd hfin (not_isFinite_linkedPlace_v2 L (φc (Classical.choose h2).1))
    · obtain ⟨q', hq'⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hfin
      obtain ⟨v, hv, σ, hσ⟩ := exists_smul_ofFinite_finQW_eq L R hRfin hRcov q'
      exact absurd (show isFinClass q from ⟨⟨v, hv⟩, by
        rw [← Quotient.out_eq q, hq']
        exact Quotient.sound ⟨σ, hσ⟩⟩) h1

end LinkedTransversal

section InertiaTrivial

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The inertia of a level at a place unramified in it is trivial.**  If the finite place `A` of
`Ω` is unramified in the finite Galois level `L`, then the inertia subgroup of `Gal(L/k)` at the
prime `finQW L A hA` of `𝓞 L` below `A` is trivial. -/
theorem inertiaAt_finQW_eq_one_of_not_ramified_v2
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunr : ¬ SSGRoute.IsRamifiedIn k L A) :
    ∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L A hA) σ → σ = 1 := by
  classical
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI hnorm : Normal k ↥L := inferInstance
  -- `finQW L A hA` is the prime of `𝓞 L` below `A`
  have hq : Work.SSGRoute.PT.finQW L A hA = Work.SSGRoute.levelPrime k Ω A hA L := by
    refine IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have harg : ((x : ↥L) : Ω)
        = algebraMap ↥L Ω (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x) := rfl
    rw [Work.SSGRoute.PT.finQW_spec L A hA x,
      Work.SSGRoute.primeOfLevel_mem_iff_k k Ω A hA L x,
      IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L Ω x, harg]
  -- the level inertia is the image of the place inertia
  have hmap := Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L
  have hle : Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup := by
    intro δ hδ
    by_contra hδ'
    exact hunr ⟨δ, (Work.SSGRoute.mem_inertiaSub k Ω A δ).mp hδ, hδ'⟩
  intro σ hσ
  rw [hq] at hσ
  rw [Work.SSGRoute.PT.isInertiaAt_iff_mem_inertia_local] at hσ
  have hσ' : σ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA L := hσ
  rw [← hmap] at hσ'
  have hbot : (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom ↥L) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hx
    exact MonoidHom.mem_ker.mp (by
      rw [IntermediateField.restrictNormalHom_ker]
      exact hle hδ)
  rw [hbot] at hσ'
  exact Subgroup.mem_bot.mp hσ'

end InertiaTrivial

/-- Piece V⁺ of `finiteS_converse_canonical_v6`: the value formula at all places (restates
`PT.valueFormula_arch` with the v6 binders: `hC1`, the seam `φc`/`hseam`, and the all-level
`hpairArch`; the conclusion is unchanged).

Route: v4's `valueFormula_abstract` with the archimedean places added.
* `phiAt (extToClasses X) h = pairK (extToClasses Z) h`, where `Z` is the level-`L` transfer of `X`
  (`phiAt_extToClasses_eq_idleRepMap`), decomposed over a transversal of the places of `L` by
  `chi_pairK_eq_sum_iota`.
* Choose the transversal to contain `u_c := mk (φc c |_L)` for each `c ∈ C`.  This is possible:
  * `liesOver_linked`: `u_c | wc c`;
  * `decompK_linked` at `L`: `D_{u_c} = ⟨res_L c⟩`;
  * `wc_orbit_injective`: distinct orbits.
* Finite terms: `vf_local_compare` + `hpair`, as in v4.
* Term at `u_c`: `extLoc u_c Z = levelPair-transport of extLoc (wc c) X`
  (`E7cOmega.extLoc_push_ideleMap`, any place, with `ι := localUnitsMap`).  So
  `yonedaPair (extLoc u_c Z) (extHRestrict D_{u_c} h)` is literally
  `levelPair (decompKRestrict …) (localUnitsMap …) (βc c (β c)) (extHRestrict D_{u_c} h)`
  (unfold `yonedaPair`, `levelPair`).
* `hpairArch` at level `L`, with `ψ` a cocycle of `h` and `b := ψ ∘ res_L`, turns that term into
  `pair ⟨c⟩ (β c) b`.
* Every other place of `L` lies over a place of `K` where `X` has component `0`, so its term
  vanishes.
* The level-independence of the archimedean pairing is NOT needed here: `hpairArch` is assumed at
  every level.  Whoever instantiates `pair` (the G1⁺ hub) owes it. -/
theorem valueFormula_arch_own_v2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (hpair_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        pair (SSGRoute.decomp k A) a b = 0)
    (hreal_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
        (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          lam (b + b') = lam b + lam b') →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
        ∃ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
          ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            pair (SSGRoute.decomp k A) a b = lam b)
    (βg : ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        (SSGRoute.PTExt.unitsK k ↥K) 1)
    (hβg_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      βg (b + b') = βg b + βg b')
    (hβg_ker : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (βg b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b))
    (hβg_onto : ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
      SSGRoute.IsLocConstOn ⊤ b ∧ βg b = y)
    (hsq : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βl A hA b)
    (wc : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K)
    (βc : ∀ c : (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (wc c)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (wc c)) 1)
    (hwc : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        wc c ≠ NK.GlobalCFT.Place.ofFinite q) ∧
      (Subgroup.zpowers c).map (SSGRoute.res k K) = SSGRoute.PTExt.decompK (k := k) (wc c))
    (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hseam : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x)) ∧
      wc c = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))))
    (hβc_add : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
      βc c (b + b') = βc c b + βc c b')
    (hβc_ker : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      (βc c b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (hβc_onto : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc c b = y)
    (hβc_sq : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) (wc c)
        (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βc c b)
    (hpairArch : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
          (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (wc c))
          (hus : u = NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥L) Ω))))
          (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
          (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g),
          (∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) →
          pair (Subgroup.zpowers c) a b =
            χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u
              (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
                (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
                  (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)))))
    (S₁ : Finset (ValuationSubring Ω)) (hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A)
    (hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B)
    (hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
    (hC1 : ∀ c ∈ C, c ≠ 1)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b +
        ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0)
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRdisj : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (hRcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B)
    (αe : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hαe : ∀ v ∈ R, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v) (αe v) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v) (αe v))
    (hαeunr : {v : ValuationSubring Ω | v ∈ R ∧
      ¬ ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → αe v σ = 0}.Finite)
    (X : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) (SSGRoute.PTExt.idelesK k ↥K) 1)
    (hX : (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
            SSGRoute.PTExt.extLoc (k := k)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X =
            βl v (hRfin v hv) (αe v)) ∧
          (∀ c ∈ C, SSGRoute.PTExt.extLoc (k := k) (wc c) X = βc c (β c)) ∧
          (∀ w : NK.GlobalCFT.Place ↥K,
            (∀ (v : ValuationSubring Ω) (hv : v ∈ R) (σ : ↥K ≃ₐ[k] ↥K),
              σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) ≠ w) →
            (∀ c ∈ C, ∀ σ : ↥K ≃ₐ[k] ↥K, σ • wc c ≠ w) →
              SSGRoute.PTExt.extLoc (k := k) w X = 0)) :

    ∀ (L : IntermediateField (↥K) Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) ↥L)
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) 1),
      ∃ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
        (((∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R), pair (SSGRoute.decomp k v) (αe v) b)
            + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b) = 0 →
          SSGRoute.PTExt.phiAt (k := k) (K := ↥K) (L := ↥L)
            (SSGRoute.PTExt.extToClasses (k := k) X) h = 0) := by
  classical
  intro L hLnum hLfd hLgal h
  haveI := hLnum
  haveI := hLfd
  haveI := hLgal
  -- the level `L` as an `IntermediateField k Ω` (its carrier is unchanged)
  let Lk : IntermediateField k Ω := IntermediateField.restrictScalars k L
  letI hnumLk : NumberField ↥Lk := (inferInstance : NumberField ↥L)
  letI hfdLk : FiniteDimensional k ↥Lk := (inferInstance : FiniteDimensional k ↥L)
  letI hgalLk : IsGalois k ↥Lk := (inferInstance : IsGalois k ↥L)
  letI hAlgKL : Algebra ↥K ↥Lk := (inferInstance : Algebra ↥K ↥L)
  letI hST1 : IsScalarTower k ↥K ↥Lk :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
      rw [IntermediateField.coe_algebraMap_apply]
      have hrew : ((algebraMap ↥K ↥Lk (algebraMap k ↥K x) : ↥Lk) : Ω)
          = algebraMap ↥K Ω (algebraMap k ↥K x) :=
        (congrArg Subtype.val (show (algebraMap ↥K ↥Lk (algebraMap k ↥K x) : ↥Lk)
            = (algebraMap ↥K ↥L (algebraMap k ↥K x) : ↥L) from rfl)).trans
          (IntermediateField.coe_algebraMap_apply (S := L) (algebraMap k ↥K x))
      rw [hrew]
      exact (IsScalarTower.algebraMap_apply k ↥K Ω x).symm)
  letI hST2 : IsScalarTower ↥K ↥Lk Ω :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hKLk : K ≤ Lk := fun x hx => L.algebraMap_mem (⟨x, hx⟩ : ↥K)
  -- ## the representative of the class `h`
  obtain ⟨ψ, hψ, b, hbψ, hclass, hbc, hbl⟩ :=
    Work.SSGRoute.PT.vf_exists_rep p k Ω K T M Lk h
  refine ⟨b, hbc, hbl, ?_⟩
  intro hsum
  -- ## the level where `b` is unramified
  obtain ⟨U, hUo, hUloc⟩ := hbl
  obtain ⟨N, hNfd, hNnorm, hKN, hNU⟩ :=
    Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K U hUo
  haveI hNgal : IsGalois k ↥N :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hNnf : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField N
  -- ## the finite set of places where `αe` fails to vanish on inertia
  let Sbad : Set (ValuationSubring Ω) :=
    {v : ValuationSubring Ω | v ∈ R ∧
      ¬ ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → αe v σ = 0}
  have hSbadfin : Sbad.Finite := hαeunr
  have hSbadR : ∀ v ∈ Sbad, v ∈ R := fun _ hv => hv.1
  -- ## the bad finite set of places of `R`
  obtain ⟨Rbad1, hRbad1R, hRbad1⟩ :=
    Work.SSGRoute.PT.vf_bad_finset K Lk hKLk p R hRfin hRdisj hRcov Sbad (fun v hv => hv.1) hSbadfin
  obtain ⟨Rbad2, hRbad2R, hRbad2⟩ :=
    Work.SSGRoute.PT.vf_bad_finset K N hKN p R hRfin hRdisj hRcov (∅ : Set (ValuationSubring Ω))
      (by simp) Set.finite_empty
  let Rbad : Finset (ValuationSubring Ω) := Rbad1 ∪ Rbad2
  have hRbadR : ∀ v ∈ Rbad, v ∈ R := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hRbad1R v h
    · exact hRbad2R v h
  have hbad_p : ∀ v ∈ R, v.valuation (p : Ω) < 1 → v ∈ Rbad := fun v hv hp =>
    Finset.mem_union_left _ (hRbad1 v hv (Or.inl hp))
  have hbad_K : ∀ v ∈ R, SSGRoute.IsRamifiedIn k K v → v ∈ Rbad := fun v hv hh =>
    Finset.mem_union_left _ (hRbad1 v hv (Or.inr (Or.inl hh)))
  have hbad_L : ∀ v ∈ R, SSGRoute.IsRamifiedIn k Lk v → v ∈ Rbad := fun v hv hh =>
    Finset.mem_union_left _ (hRbad1 v hv (Or.inr (Or.inr (Or.inl hh))))
  have hbad_N : ∀ v ∈ R, SSGRoute.IsRamifiedIn k N v → v ∈ Rbad := fun v hv hh =>
    Finset.mem_union_right _ (hRbad2 v hv (Or.inr (Or.inr (Or.inl hh))))
  have hbad_S : ∀ v ∈ R, v ∈ Sbad → v ∈ Rbad := fun v hv hh =>
    Finset.mem_union_left _ (hRbad1 v hv (Or.inr (Or.inr (Or.inr hh))))
  -- ## the transversal of the places of `L` containing the linked places
  obtain ⟨R'', hR''fin, hR''link, hR''uniq, hR''inj, hR''fr⟩ :=
    Work.SSGRoute.PT.exists_transversal_linked_v2 K Lk R hRfin hRdisj hRcov C φc hCinv hC1
      (fun c hc x => (hseam c (hCinv c hc) (hC1 c hc)).1 x) hCdisj
  -- ## the glued class at level `L`
  let Z : Abelian.Ext (Rep.res (galRes k (↥K) (↥Lk))
      (modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))
      (SSGRoute.PTExt.idelesK k ↥Lk) 1 :=
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥Lk)) X).comp
      (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥Lk))) (add_zero 1)
  -- ## the two families of representatives
  let wv : {v : ValuationSubring Ω // v ∈ R} → ↥R'' := fun v =>
    ⟨NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v.1 (hRfin v.1 v.2)), hR''fin v.1 v.2⟩
  let wc₀ : {c : Ω ≃ₐ[k] Ω // c ∈ C} → ↥R'' := fun c =>
    ⟨linkedPlace_v2 Lk (φc c.1), hR''link c.1 c.2⟩
  let wvR : {v : ValuationSubring Ω // v ∈ Rbad} → ↥R'' := fun v => wv ⟨v.1, hRbadR v.1 v.2⟩
  -- ## the finite set `T` of places of `L` carrying the whole sum
  let Tset : Finset ↥R'' := (Rbad.attach.image wvR) ∪ (C.attach.image wc₀)
  -- ## the value of the summand
  let Xt : ↥R'' → ZMod p := fun w =>
    χ Lk hKLk (Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) w.1
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h)))
  -- ## membership in `T`
  have hmem_wv : ∀ v : ↥Rbad, wvR v ∈ Tset := by
    intro v
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_attach _ v, rfl⟩)
  have hmem_wc : ∀ c : ↥C, wc₀ c ∈ Tset := by
    intro c
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_attach _ c, rfl⟩)
  -- ## the places of `R` outside `Rbad` are good
  have hgood : ∀ v ∈ R, v ∉ Rbad → ¬ v.valuation (p : Ω) < 1 ∧
      ¬ SSGRoute.IsRamifiedIn k K v ∧ ¬ SSGRoute.IsRamifiedIn k Lk v ∧
      ¬ SSGRoute.IsRamifiedIn k N v ∧ v ∉ Sbad := by
    intro v hv hvbad
    exact ⟨fun h => hvbad (hbad_p v hv h), fun h => hvbad (hbad_K v hv h),
      fun h => hvbad (hbad_L v hv h), fun h => hvbad (hbad_N v hv h),
      fun h => hvbad (hbad_S v hv h)⟩
  -- ## `b` vanishes on inertia outside `Rbad`
  have hb_one : b 1 = 0 := by
    have h := hbc 1 trivial 1 trivial
    have h' : b 1 + b 1 = b 1 := by simpa using h.symm
    exact add_left_cancel (by rw [add_zero]; exact h')
  have hb_inertia : ∀ v ∈ R, v ∉ Rbad → ∀ σ : (Ω ≃ₐ[k] Ω),
      SSGRoute.IsInertia k v σ → b σ = 0 := by
    intro v hv hvbad σ hσ
    obtain ⟨-, -, -, hunrN, -⟩ := hgood v hv hvbad
    have hfix : σ ∈ N.fixingSubgroup := by
      by_contra h
      exact hunrN ⟨σ, hσ, h⟩
    have hU : σ ∈ U := hNU hfix
    calc b σ = b (1 * σ) := by rw [one_mul]
      _ = b 1 := hUloc 1 trivial σ hU trivial
      _ = 0 := hb_one
  -- ## `αe` vanishes on inertia outside `Rbad`
  have hα_inertia : ∀ v ∈ R, v ∉ Rbad → ∀ σ : (Ω ≃ₐ[k] Ω),
      SSGRoute.IsInertia k v σ → αe v σ = 0 := by
    intro v hv hvbad σ hσ
    obtain ⟨-, -, -, -, hS⟩ := hgood v hv hvbad
    by_contra hne
    exact hS ⟨hv, fun h => hne (h σ hσ)⟩
  -- ## the identification of the finite terms
  have hfin_id : ∀ (A : ValuationSubring Ω) (hA : A ∈ R),
      χ Lk hKLk (Work.SSGRoute.PT.iota (k := k) (L := ↥Lk)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk A (hRfin A hA)))
        (SSGRoute.PTExt.yonedaPair
          (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk A (hRfin A hA))) Z)
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk A (hRfin A hA)))) h)))
      = pair (SSGRoute.decomp k A) (αe A) b := by
    intro A hA
    have hbA : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
      fun g _ h _ => hbc g trivial h trivial
    have hlA : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b :=
      ⟨U, hUo, fun g _ u hu _ => hUloc g trivial u hu trivial⟩
    have hb₀A : ∀ σ ∈ SSGRoute.decomp k A, b σ = ψ (AlgEquiv.restrictNormalHom Lk σ) :=
      fun σ _ => hbψ σ
    have hcmp := Work.SSGRoute.PT.vf_local_compare p k Ω K T M Lk hKLk A (hRfin A hA) X
      (βl A (hRfin A hA) (αe A)) (hX.1 A hA) h ψ hψ hclass b hbψ hbA hb₀A
    have hp := hpair A (hRfin A hA) (αe A) b (hαe A hA).2 hlA hbA Lk hKLk ψ hb₀A
    rw [hcmp, hp]
  -- ## the identification of the archimedean terms
  have harch_id : ∀ c ∈ C,
      χ Lk hKLk (Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) (linkedPlace_v2 Lk (φc c))
        (SSGRoute.PTExt.yonedaPair
          (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) (linkedPlace_v2 Lk (φc c)) Z)
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (linkedPlace_v2 Lk (φc c))) h)))
      = pair (Subgroup.zpowers c) (β c) b := by
    intro c hc
    have hc2 : c ^ 2 = 1 := hCinv c hc
    have hc1 : c ≠ 1 := hC1 c hc
    have hlies : NK.GlobalCFT.Place.LiesOver (linkedPlace_v2 Lk (φc c)) (wc c) :=
      (hseam c hc2 hc1).2.symm ▸ linkedPlace_liesOver_v2 K Lk (φc c)
    have hloc : SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) (linkedPlace_v2 Lk (φc c)) Z
        = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k (↥K) (↥Lk) (wc c)
              (linkedPlace_v2 Lk (φc c)) hlies)
            (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) (wc c) X)).comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k (↥K) (↥Lk) (wc c)
            (linkedPlace_v2 Lk (φc c)) hlies)) (add_zero 1) := by
      rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥Lk) (z := X)
        (u := wc c) (w := linkedPlace_v2 Lk (φc c)) (hw := hlies)
        (ι := Work.SSGRoute.localUnitsMap k (↥K) (↥Lk) (wc c) (linkedPlace_v2 Lk (φc c)) hlies)
        (hι := Work.SSGRoute.localUnitsMap_spec k (↥K) (↥Lk) (wc c)
          (linkedPlace_v2 Lk (φc c)) hlies)]
    have hXc : SSGRoute.PTExt.extLoc (k := k) (K := ↥K) (wc c) X = βc c (β c) := hX.2.1 c hc
    have harch := hpairArch c hc2 hc1 (β c) b (hβ c hc) Lk hKLk (linkedPlace_v2 Lk (φc c))
      hlies rfl ψ hψ (fun σ _ => hbψ σ)
    rw [hloc, hXc, hclass]
    exact harch.symm

  -- ## the `p`-torsion of the local `ι`-values
  have hptor : ∀ x : Work.SSGRoute.PT.VFcoef p M T, p • x = 0 :=
    fun x => Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p x
  have iota_nsmul : ∀ (w : NK.GlobalCFT.Place ↥Lk)
      (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥Lk) w) 2) (n : ℕ),
      n • Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) w z
        = Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) w (n • z) := fun w z n =>
    (AddMonoidHom.map_nsmul
      { toFun := fun z => Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) w z
        map_zero' := Work.SSGRoute.PT.iota_zero w
        map_add' := fun a b => Work.SSGRoute.PT.iota_add w a b } n z).symm
  have hp : ∀ w : ↥R'', p • Work.SSGRoute.PT.iota (k := k) (L := ↥Lk) w.1
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h)) = 0 := by
    intro w
    have hy : p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h) = 0 := by
      have h1 : p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h)
          = SSGRoute.PTExt.yonedaPair (p • SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
            (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h) :=
        (AddMonoidHom.map_nsmul
          { toFun := fun x => SSGRoute.PTExt.yonedaPair x
              (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h)
            map_zero' := SSGRoute.PTExt.yonedaPair_zero_right _
            map_add' := fun x x' => SSGRoute.PTExt.yonedaPair_add_right x x' _ } p
          (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)).symm
      rw [h1, Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hptor
        (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)]
      exact SSGRoute.PTExt.yonedaPair_zero_right _
    rw [iota_nsmul, hy, Work.SSGRoute.PT.iota_zero]
  -- ## the vanishing of the local pairings off `Tset`
  have hT0 : ∀ w : ↥R'', w ∉ Tset →
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z)
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w.1) h) = 0 := by
    intro w hwT
    have hmem : w ∈ Tset ↔ w ∈ Rbad.attach.image wvR ∨ w ∈ C.attach.image wc₀ := by
      show w ∈ (Rbad.attach.image wvR : Finset ↥R'') ∪ (C.attach.image wc₀) ↔ _
      rw [Finset.mem_union]
    have hwv : ¬ ∃ v : ↥Rbad, wvR v = w := by
      rintro ⟨v, hv⟩
      exact hwT (hmem.mpr (Or.inl (hv ▸ Finset.mem_image.mpr ⟨v, Finset.mem_attach _ v, rfl⟩)))
    have hwc : ¬ ∃ c : ↥C, wc₀ c = w := by
      rintro ⟨c, hc⟩
      exact hwT (hmem.mpr (Or.inr (hc ▸ Finset.mem_image.mpr ⟨c, Finset.mem_attach _ c, rfl⟩)))
    by_cases hfin : w.1.IsFinite
    · -- finite place: the level is unramified there
      obtain ⟨v, hv, hwv_eq⟩ := hR''fr w hfin
      have hvbad : v ∉ Rbad := by
        intro hvb
        refine hwv ⟨⟨v, hvb⟩, Subtype.ext ?_⟩
        rw [hwv_eq]
      obtain ⟨hgp, hgK, hgL, -, -⟩ := hgood v hv hvbad
      have hu' : NK.GlobalCFT.Place.LiesOver
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv)))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) :=
        (Work.SSGRoute.PT.place_glue_level k Ω K Lk hKLk v (hRfin v hv)
          (Work.SSGRoute.PT.finQ K v (hRfin v hv))
          (fun x => Work.SSGRoute.PT.finQ_spec K v (hRfin v hv) x)
          (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))
          (fun y => Work.SSGRoute.PT.finQW_spec Lk v (hRfin v hv) y)).1
      have hunr : ∀ σ : ↥Lk ≃ₐ[k] ↥Lk,
          SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW Lk v (hRfin v hv)) σ → σ = 1 :=
        Work.SSGRoute.PT.inertiaAt_finQW_eq_one_of_not_ramified_v2 K Lk v (hRfin v hv) hgL
      have hpush : SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) Z
          = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k (↥K) (↥Lk)
                (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
                (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
              (SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X)).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k (↥K) (↥Lk)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu'))
            (add_zero 1) :=
        Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥Lk) (z := X)
          (u := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
          (w := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) (hw := hu')
          (ι := Work.SSGRoute.localUnitsMap k (↥K) (↥Lk)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
          (hι := Work.SSGRoute.localUnitsMap_spec k (↥K) (↥Lk)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
      rw [hwv_eq, hpush, hX.1 v hv]
      exact Work.SSGRoute.PT.levelPair_unramified_eq_zero k ↥K
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
        ↥Lk (Work.SSGRoute.PT.finQW Lk v (hRfin v hv)) hu' hunr
        (Work.SSGRoute.decompKRestrict k (↥K) (↥Lk)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
        (Work.SSGRoute.decompKRestrict_coe k (↥K) (↥Lk)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
        (Work.SSGRoute.localUnitsMap k (↥K) (↥Lk)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
        (Work.SSGRoute.localUnitsMap_spec k (↥K) (↥Lk)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv))) hu')
        (βl v (hRfin v hv) (αe v))
        (hβl_unr v (hRfin v hv) hgp hgK (αe v) (hαe v hv).1 (hαe v hv).2
          (hα_inertia v hv hvbad))
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v (hRfin v hv)))) h)
    · -- infinite place: the place of `K` below it is not conjugate to any `wc c`
      haveI : FiniteDimensional ↥K ↥Lk := FiniteDimensional.right k ↥K ↥Lk
      obtain ⟨u, hwu⟩ := Work.SSGRoute.exists_place_under (L := ↥K) (L' := ↥Lk) w.1
      have hufin : ¬ u.IsFinite := fun hu =>
        hfin ((NK.GlobalCFT.Place.isFinite_of_liesOver hwu).mpr hu)
      have hu₁ : ∀ (v : ValuationSubring Ω) (hv : v ∈ R) (σ : ↥K ≃ₐ[k] ↥K),
          σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) ≠ u := by
        intro v hv σ h
        have h1 : (σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v
            (hRfin v hv))).IsFinite := by
          rw [NK.GlobalCFT.Place.smul_ofFinite]
          exact NK.GlobalCFT.Place.isFinite_ofFinite _
        rw [h] at h1
        exact hufin h1
      have hu₂ : ∀ c ∈ C, ∀ σ : ↥K ≃ₐ[k] ↥K, σ • wc c ≠ u := by
        intro c hc σ hσ
        have hlic : NK.GlobalCFT.Place.LiesOver (linkedPlace_v2 Lk (φc c)) (wc c) :=
          (hseam c (hCinv c hc) (hC1 c hc)).2.symm ▸ linkedPlace_liesOver_v2 K Lk (φc c)
        have hveq : σ⁻¹ • u = wc c := by rw [← hσ]; simp
        have hv : NK.GlobalCFT.Place.LiesOver (linkedPlace_v2 Lk (φc c)) (σ⁻¹ • u) := by
          rw [hveq]; exact hlic
        obtain ⟨ρ, hρ⟩ := Work.SSGRoute.E7cOmega.mem_orbit_of_liesOver_conj (k := k) (K := ↥K)
          ↥Lk u w.1 hwu (linkedPlace_v2 Lk (φc c)) σ⁻¹ hv
        have h1 : ∃ τ : ↥Lk ≃ₐ[k] ↥Lk, τ • w.1 = w.1 := ⟨1, one_smul _ _⟩
        have h2 : ∃ τ : ↥Lk ≃ₐ[k] ↥Lk, τ • w.1 = (wc₀ ⟨c, hc⟩).1 := ⟨ρ, hρ⟩
        have heq : w = wc₀ ⟨c, hc⟩ := (hR''uniq w.1).unique h1 h2
        exact hwc ⟨⟨c, hc⟩, heq.symm⟩
      have hXu : SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u X = 0 := hX.2.2 u hu₁ hu₂
      have hpush : SSGRoute.PTExt.extLoc (k := k) (K := ↥Lk) w.1 Z
          = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k (↥K) (↥Lk) u w.1 hwu)
              (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u X)).comp
            (CategoryTheory.Abelian.Ext.mk₀
              (Work.SSGRoute.localUnitsMap k (↥K) (↥Lk) u w.1 hwu)) (add_zero 1) :=
        Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥Lk) (z := X)
          (u := u) (w := w.1) (hw := hwu)
          (ι := Work.SSGRoute.localUnitsMap k (↥K) (↥Lk) u w.1 hwu)
          (hι := Work.SSGRoute.localUnitsMap_spec k (↥K) (↥Lk) u w.1 hwu)
      rw [hpush, hXu, SSGRoute.PTExt.extRes_zero]
      rw [CategoryTheory.Abelian.Ext.zero_comp]
      exact SSGRoute.PTExt.yonedaPair_zero_right _
  -- ## the reindexing of the sum over `Tset`
  have hinj_v : Set.InjOn wvR ↑(Rbad.attach) := by
    intro a _ b _ hab
    have h1 : NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk a.1 (hRfin a.1 (hRbadR a.1 a.2)))
        = NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk b.1 (hRfin b.1 (hRbadR b.1 b.2))) :=
      congrArg Subtype.val hab
    exact Subtype.ext (hR''inj a.1 b.1 (hRbadR a.1 a.2) (hRbadR b.1 b.2) h1)
  have hinj_c : Set.InjOn wc₀ ↑(C.attach) := by
    intro a _ b _ hab
    have h1 : linkedPlace_v2 Lk (φc b.1) = linkedPlace_v2 Lk (φc a.1) := (congrArg Subtype.val hab).symm
    have h2 : a.1 = b.1 :=
      linkedPlace_orbit_injective_v2 K Lk C φc hCinv hC1
        (fun c hc x => (hseam c (hCinv c hc) (hC1 c hc)).1 x) hCdisj a.2 b.2 ⟨1, by
          simpa using h1⟩
    exact Subtype.ext h2
  have hdisj : Disjoint (Rbad.attach.image wvR) (C.attach.image wc₀) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hw2
    have h1 : (wvR v).1.IsFinite := by
      show (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW Lk v.1
        (hRfin v.1 (hRbadR v.1 v.2)))).IsFinite
      exact NK.GlobalCFT.Place.isFinite_ofFinite _
    rw [← hc] at h1
    exact not_isFinite_linkedPlace_v2 Lk (φc c.1) h1
  have hreindex : (∑ w ∈ Tset, Xt w)
      = (∑ v ∈ Rbad, pair (SSGRoute.decomp k v) (αe v) b)
        + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b := by
    rw [show Tset = (Rbad.attach.image wvR) ∪ (C.attach.image wc₀) from rfl,
      Finset.sum_union hdisj, Finset.sum_image (f := Xt) hinj_v,
      Finset.sum_image (f := Xt) hinj_c]
    have hv : (∑ x ∈ Rbad.attach, Xt (wvR x))
        = ∑ x ∈ Rbad, pair (SSGRoute.decomp k x) (αe x) b := by
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Rbad.attach) => hfin_id x.1 (hRbadR x.1 x.2)),
        Finset.sum_attach Rbad (fun v => pair (SSGRoute.decomp k v) (αe v) b)]
    have hc : (∑ x ∈ C.attach, Xt (wc₀ x))
        = ∑ x ∈ C, pair (Subgroup.zpowers x) (β x) b := by
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ C.attach) => harch_id x.1 x.2),
        Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β c) b)]
    rw [hv, hc]
  -- ## the finite sum over `R` is the sum over `Rbad`
  have hfinsum : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R),
        pair (SSGRoute.decomp k v) (αe v) b)
      = ∑ v ∈ Rbad, pair (SSGRoute.decomp k v) (αe v) b := by
    refine finsum_mem_eq_sum_of_subset (fun v => pair (SSGRoute.decomp k v) (αe v) b) ?_ ?_
    · intro v hv
      obtain ⟨hvR, hsupp⟩ := hv
      by_contra hvb
      exact (Function.mem_support.mp hsupp) (by
        rw [hpair_unr v (hRfin v hvR) (hgood v hvR hvb).1 (hgood v hvR hvb).2.1
          (αe v) b (hα_inertia v hvR hvb) (hb_inertia v hvR hvb)])
    · intro v hv
      exact hRbadR v hv
  -- ## the value of the class-level pairing, and its vanishing
  have hchi : χ Lk hKLk (SSGRoute.PTExt.yonedaPair
      (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) h) = ∑ w ∈ Tset, Xt w :=
    Work.SSGRoute.PT.chi_pairK_eq_sum_iota p (χ Lk hKLk) (hχadd Lk hKLk) R'' hR''uniq Z h
      Tset hT0 hp
  have hχ0 : χ Lk hKLk (SSGRoute.PTExt.yonedaPair
      (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) h) = 0 := by
    rw [hchi, hreindex, ← hfinsum]
    exact hsum
  -- ## the `p`-torsion of the class-level pairing
  have hpt : p • SSGRoute.PTExt.yonedaPair
      (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) h = 0 := by
    have hph : p • h = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor h
    have h1 : p • SSGRoute.PTExt.yonedaPair
        (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) h
        = SSGRoute.PTExt.yonedaPair
          (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) (p • h) :=
      (AddMonoidHom.map_nsmul
        { toFun := fun h' => SSGRoute.PTExt.yonedaPair
            (SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk) Z) h'
          map_zero' := SSGRoute.PTExt.yonedaPair_zero_left _
          map_add' := fun a b' => SSGRoute.PTExt.yonedaPair_add_left _ a b' } p h).symm
    rw [h1, hph]
    exact SSGRoute.PTExt.yonedaPair_zero_left _
  -- ## `phiAt` is the class-level pairing with the transferred class
  rw [Work.SSGRoute.phiAt_extToClasses_eq_idleRepMap k ↥K ↥L _ X h,
    Work.SSGRoute.levelPair_eq_yonedaPair]
  change SSGRoute.PTExt.extToClasses (k := k) (K := ↥Lk)
      (SSGRoute.PTExt.yonedaPair Z h) = 0
  rw [← Work.SSGRoute.PT.extToClasses_yonedaPair (k := k) (K := ↥Lk) Z h]
  exact hχinj Lk hKLk _ hpt hχ0

end Work.SSGRoute.PT
