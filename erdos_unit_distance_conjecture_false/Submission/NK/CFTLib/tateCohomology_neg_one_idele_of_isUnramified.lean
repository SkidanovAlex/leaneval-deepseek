import Mathlib
import Submission.NK.CFTLib.roquetteDefs
import Submission.NK.CFTLib.roquette_plan
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_unitIdelesOutsideRep
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_decompositionSubgroup_ofInfinite_eq_finrank
import Submission.NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_ideleRep
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot
import Submission.NK.CFTLib.subsingleton_tateCohomology_neg_one_of_coind
import Submission.NK.CFTLib.subsingleton_tateCohomology_neg_one_of_cover
import Submission.NK.CFTLib.subsingleton_tateCohomology_of_shortExact_middle
import Submission.NK.CFTLib.localUnitSubRep_tateCohomology_neg_one_of_ramificationIdx_eq_one
import Submission.NK.CFTLib.integralIdelesLeNormImage

/-!
# Step 1 of Roquette's idèle computation: `Ĥ⁻¹(Gal(K/F), 𝕀_K) = 0` for `K/F` unramified
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-! ## Local inputs -/

/-- **Cyclicity of a decomposition group of an unramified place**, transported from cyclicity of
the local Galois group. -/
theorem isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
  (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq).isCyclic.mpr
    (Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q q hq hunr)

/-- **`Ĥ⁻¹(D_q, L_qˣ) = 0` for an unramified finite place `q`.**  The decomposition group is
cyclic, so `Ĥ⁻¹ ≅ Ĥ¹`, and `Ĥ¹(D_q, L_qˣ) = 0` is Hilbert 90. -/
theorem subsingleton_tateCohomology_neg_one_localUnitsRep_of_ramificationIdx_eq_one {K L : Type}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q)) (-1)) := by
  haveI := isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one Q q hq hunr
  exact NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
    _ (NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_localUnitsRep
        (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))

/-! ## Transport of vanishing along an isomorphism of representations -/

/-- Vanishing of Tate cohomology is invariant under isomorphism of representations. -/
theorem subsingleton_tateCohomology_of_iso {G : Type} [Group G] [Fintype G] {M N : Rep ℤ G}
    (e : M ≅ N) (r : ℤ) (h : Subsingleton (tateCohomology M r)) :
    Subsingleton (tateCohomology N r) :=
  (Equiv.subsingleton_congr
    (((tateCohomologyFunctor (R := ℤ) (G := G) r).mapIso e).toLinearEquiv.toEquiv)).mp h

/-! ## The fibres, from the local computations -/

/-- **The fibre at `v` has vanishing `Ĥ⁻¹` as soon as the local field units `L_wˣ` do**: the fibre
is `Coind_{D_w}^G L_wˣ` (Shapiro) and `Ĥ⁻¹` of a coinduced module is that of the module. -/
theorem subsingleton_tateCohomology_neg_one_fiberIdelesRep_of_local {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (v : Place K) (w : Place L) (hw : Place.LiesOver w v)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)]
    (h : Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) (-1))) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v) (-1)) := by
  obtain ⟨e⟩ := NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind (K := K) (L := L) v w hw
  have h' : Subsingleton (tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w).subtype
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w)) (-1)) :=
    subsingleton_tateCohomology_neg_one_of_coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) h
  exact subsingleton_tateCohomology_of_iso e.symm (-1) h'

/-- **The unit fibre at `v` has vanishing `Ĥ⁻¹` as soon as the local units `𝒪_wˣ` do**: the unit
fibre is `Coind_{D_w}^G 𝒪_wˣ`. -/
theorem subsingleton_tateCohomology_neg_one_fiberUnitsRep_of_local {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (v : Place K) (q : HeightOneSpectrum (𝓞 L))
    (hw : Place.LiesOver (Place.ofFinite q) v)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))]
    (h : Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) (-1))) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) (-1)) := by
  obtain ⟨e⟩ := NK.GlobalCFTdeep.fiberUnitsRep_iso_coind (K := K) (L := L) v q hw
  have h' : Subsingleton (tateCohomology (Rep.coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)).subtype
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (Place.ofFinite q))) (-1)) :=
    subsingleton_tateCohomology_neg_one_of_coind
      (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) h
  exact subsingleton_tateCohomology_of_iso e.symm (-1) h'

/-! ## The `T`-idèles -/

/-- **The idèles supported on a finite union of fibres have vanishing `Ĥ⁻¹`.** -/
theorem subsingleton_tateCohomology_neg_one_supportedIdelesRep {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (h : ∀ v : Place K, Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v) (-1))) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) (-1)) := by
  have hcard := NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
    (K := K) (L := L) S T hT hTS (-1)
  haveI hv : ∀ v : ↥S, Subsingleton ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : Place K)) (-1)) :=
    fun v => h (v : Place K)
  haveI : Subsingleton ((v : ↥S) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : Place K)) (-1))) :=
    inferInstance
  haveI : Nonempty ((v : ↥S) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : Place K)) (-1))) :=
    ⟨fun _ => 0⟩
  have hone : Nat.card ((v : ↥S) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : Place K)) (-1))) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [hone] at hcard
  haveI : Nonempty ↑(tateCohomology
      (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) (-1)) := ⟨0⟩
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

/-- **The unit idèles outside `T` have vanishing `Ĥ⁻¹`** if every unit fibre outside `S` does. -/
theorem subsingleton_tateCohomology_neg_one_unitIdelesOutsideRep {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S)
    (h : ∀ v : Place K, Place.IsFinite v → Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) (-1))) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) (-1)) := by
  obtain ⟨e⟩ := NK.GlobalCFTdeep.Herbrand.unitIdelesOutsideRep_iso_piRep
    (K := K) (L := L) S T hT hTS
  have hcard := NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep
    (G := L ≃ₐ[K] L) (fun v : {v : Place K // v ∉ S} =>
      NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K)) (-1)
  haveI hv : ∀ v : {v : Place K // v ∉ S}, Subsingleton ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K)) (-1)) := by
    rintro ⟨v, hv⟩
    rcases v with a | Q
    · exact absurd (hSinf a) hv
    · exact h (Place.ofFinite Q) (Place.isFinite_ofFinite Q)
  haveI : Subsingleton ((v : {v : Place K // v ∉ S}) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K)) (-1))) :=
    inferInstance
  haveI : Nonempty ((v : {v : Place K // v ∉ S}) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K)) (-1))) :=
    ⟨fun _ => 0⟩
  have hone : Nat.card ((v : {v : Place K // v ∉ S}) → ↑(tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K)) (-1))) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [hone] at hcard
  have hzero : Subsingleton (tateCohomology
      (NK.RepresentationTheory.GroupCohomology.piRep (fun v : {v : Place K // v ∉ S} =>
        NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K))) (-1)) := by
    haveI : Nonempty ↑(tateCohomology
        (NK.RepresentationTheory.GroupCohomology.piRep (fun v : {v : Place K // v ∉ S} =>
          NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) (v : Place K))) (-1)) := ⟨0⟩
    exact (Nat.card_eq_one_iff_unique.mp hcard).1
  exact subsingleton_tateCohomology_of_iso e.symm (-1) hzero

/-- **The `T`-idèles have vanishing `Ĥ⁻¹`** from the two factors of the decomposition. -/
theorem subsingleton_tateCohomology_neg_one_tIdelesRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (h1 : Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) (-1)))
    (h3 : Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) (-1))) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.tIdelesRep (L := L) T hT) (-1)) :=
  subsingleton_tateCohomology_of_shortExact_middle
    (NK.GlobalCFTdeep.Herbrand.NatCardSES.ses (L := L) T hT)
    (NK.GlobalCFTdeep.Herbrand.NatCardSES.ses_shortExact (L := L) T hT) (-1) h1 h3

/-! ## The covering family of `T`-idèles inside the idèles -/

section Assembly

open NK.GlobalCFTdeep
open NK.GlobalCFT.Inclusion

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]

/-- The finite set of infinite places of `F`. -/
noncomputable def infPlaces (F : Type) [Field F] [NumberField F] : Finset (Place F) := by
  classical exact Finset.univ.image (Place.ofInfinite (K := F))

/-- `S` together with all infinite places of `F`. -/
noncomputable def coverSet (S : Finset (Place F)) : Finset (Place F) := by
  classical exact S ∪ infPlaces F

/-- The places of `K` lying above the places in a finite set `S` of places of `F`. -/
def aboveSet (S : Finset (Place F)) : Set (Place K) := {w | ∃ v ∈ S, Place.LiesOver w v}

/-- `aboveSet S` is stable under `Gal(K/F)`. -/
theorem aboveSet_stable (S : Finset (Place F)) :
    ∀ (σ : K ≃ₐ[F] K) ⦃w : Place K⦄, w ∈ aboveSet S → σ • w ∈ aboveSet S := by
  rintro σ w ⟨v, hv, hw⟩
  exact ⟨v, hv, (Place.liesOver_smul_iff (σ := σ)).mpr hw⟩

/-- The morphism `𝕀_{K,T} ⟶ 𝕀_K` of `ℤ[Gal(K/F)]`-modules given by the inclusion. -/
noncomputable def tIdelesToIdeleRep (T : Set (Place K))
    (hT : ∀ (σ : K ≃ₐ[F] K) ⦃w : Place K⦄, w ∈ T → σ • w ∈ T) :
    NK.GlobalCFTdeep.tIdelesRep (L := K) T hT ⟶ NK.CFTLib.ideleRep F K :=
  letI : MulDistribMulAction (K ≃ₐ[F] K) ↥(NK.GlobalCFTdeep.TIdeles (L := K) T) :=
    NK.GlobalCFTdeep.stableMulDistribMulAction (K ≃ₐ[F] K) _
      (fun σ x hx => NK.GlobalCFTdeep.smul_mem_TIdeles hT hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (Subgroup.inclusion le_top (Additive.toMul x))
      map_add' := by
        intro x y
        rw [toMul_add, map_mul, Subgroup.coe_mul, ofMul_mul]
      map_smul' := by
        intro n x
        rw [toMul_zsmul, map_zpow, Subgroup.coe_zpow, ofMul_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        rfl }

/-- The underlying function of `tIdelesToIdeleRep`. -/
theorem tIdelesToIdeleRep_apply (T : Set (Place K))
    (hT : ∀ (σ : K ≃ₐ[F] K) ⦃w : Place K⦄, w ∈ T → σ • w ∈ T)
    (x : (NK.GlobalCFTdeep.tIdelesRep (L := K) T hT).V) :
    (tIdelesToIdeleRep (F := F) (K := K) T hT).hom x =
      Additive.ofMul ((Subgroup.inclusion (le_top : NK.GlobalCFTdeep.TIdeles (L := K) T ≤ ⊤)
        (Additive.toMul x) : Idele K)) := rfl

/-- The inclusion `𝕀_{K,T} ⟶ 𝕀_K` is injective. -/
theorem tIdelesToIdeleRep_injective (T : Set (Place K))
    (hT : ∀ (σ : K ≃ₐ[F] K) ⦃w : Place K⦄, w ∈ T → σ • w ∈ T) :
    Function.Injective (⇑(tIdelesToIdeleRep (F := F) (K := K) T hT).hom :
      (NK.GlobalCFTdeep.tIdelesRep (L := K) T hT).V → (NK.CFTLib.ideleRep F K).V) := by
  intro x y hxy
  have h2 : Additive.ofMul ((Subgroup.inclusion (le_top : NK.GlobalCFTdeep.TIdeles (L := K) T ≤ ⊤)
      (Additive.toMul x) : Idele K)) =
      Additive.ofMul ((Subgroup.inclusion (le_top : NK.GlobalCFTdeep.TIdeles (L := K) T ≤ ⊤)
        (Additive.toMul y) : Idele K)) := by
    rw [← tIdelesToIdeleRep_apply (F := F) (K := K) T hT x,
      ← tIdelesToIdeleRep_apply (F := F) (K := K) T hT y]
    exact hxy
  have h3 := Additive.ofMul.injective h2
  exact Additive.toMul.injective
    ((Subgroup.inclusion_injective (le_top : NK.GlobalCFTdeep.TIdeles (L := K) T ≤ ⊤))
      (Subtype.ext h3))

/-- A place of `K` below a place of `K` (with `K` viewed as an extension of `F`). -/
noncomputable def placeUnder (w : Place K) : Place F :=
  Classical.choose (globalCFT_exists_placeUnder (K := F) (L := K) w)

theorem liesOver_placeUnder (w : Place K) : Place.LiesOver w (placeUnder (F := F) w) :=
  Classical.choose_spec (globalCFT_exists_placeUnder (K := F) (L := K) w)

/-- **Every idèle lies in `𝕀_{K,T_S}` for some finite set `S` of places of `F`**: the places at
which it is not a local unit are finite. -/
theorem exists_finset_mem_tIdeles (x : Idele K) :
    ∃ S : Finset (Place F), x ∈ NK.GlobalCFTdeep.TIdeles (L := K) (aboveSet S) := by
  classical
  have hfin : ({w : Place K | x w ∉ Place.localUnits K w} : Set (Place K)).Finite :=
    Filter.eventually_cofinite.mp x.2
  refine ⟨hfin.toFinset.image (placeUnder (F := F)), fun w hw => ?_⟩
  by_contra hcon
  have hw' : placeUnder (F := F) w ∈ (hfin.toFinset.image (placeUnder (F := F))) :=
    Finset.mem_image.mpr ⟨w, hfin.mem_toFinset.mpr hcon, rfl⟩
  exact hw ⟨placeUnder (F := F) w, hw', liesOver_placeUnder (F := F) w⟩

/-- **The idèles are covered by the `T`-idèles over finite sets of places of `F`.** -/
theorem subsingleton_tateCohomology_neg_one_ideleRep_of_fibers
    (hfib : ∀ v : Place F, Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K) v) (-1)))
    (hunit : ∀ v : Place F, Place.IsFinite v → Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1))) :
    Subsingleton (tateCohomology (NK.CFTLib.ideleRep F K) (-1)) := by
  classical
  refine subsingleton_tateCohomology_neg_one_of_cover (NK.CFTLib.ideleRep F K)
    (fun S : Finset (Place F) =>
      NK.GlobalCFTdeep.tIdelesRep (L := K) (aboveSet (coverSet S)) (aboveSet_stable _))
    (fun S => tIdelesToIdeleRep (F := F) (K := K) (aboveSet (coverSet S)) (aboveSet_stable _))
    (fun S => tIdelesToIdeleRep_injective (F := F) (K := K) (aboveSet (coverSet S))
      (aboveSet_stable _))
    ?_ ?_
  · intro x
    obtain ⟨S, hx⟩ := exists_finset_mem_tIdeles (F := F) (K := K) (Additive.toMul x)
    refine ⟨S, Additive.ofMul ⟨Additive.toMul x, ?_⟩, rfl⟩
    refine NK.GlobalCFTdeep.mem_TIdeles.mpr fun w hw =>
      NK.GlobalCFTdeep.mem_TIdeles.mp hx w fun hwS => hw ?_
    obtain ⟨v, hv, hwv⟩ := hwS
    exact ⟨v, Finset.mem_union_left (infPlaces F) hv, hwv⟩

  · intro S
    have hTS : ∀ w : Place K, w ∈ aboveSet (coverSet S) ↔
        ∃ v ∈ coverSet S, Place.LiesOver w v := fun w => Iff.rfl
    refine subsingleton_tateCohomology_neg_one_tIdelesRep (K := F) (L := K)
      (aboveSet (coverSet S)) (aboveSet_stable _) ?_ ?_
    · exact subsingleton_tateCohomology_neg_one_unitIdelesOutsideRep (K := F) (L := K)
        (coverSet S) (aboveSet (coverSet S)) (aboveSet_stable _) hTS
        (fun a => by
          rw [coverSet]
          exact Finset.mem_union_right S
            (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
        (fun v hv => hunit v hv)
    · exact subsingleton_tateCohomology_neg_one_supportedIdelesRep (K := F) (L := K)
        (coverSet S) (aboveSet (coverSet S)) (aboveSet_stable _) hTS (fun v => hfib v)

end Assembly

/-! ## The local vanishings for an unramified extension -/

section Final

open NK.GlobalCFTdeep
open NK.GlobalCFT.Inclusion

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]

/-- **`Ĥ⁻¹` vanishes for the trivial group.** -/
theorem subsingleton_tateCohomology_neg_one_of_subsingleton_group {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton (tateCohomology M (-1)) := by
  classical
  letI : Module ℤ M.V := M.hV2
  have hcard : Fintype.card G = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨1, fun g => Subsingleton.elim g 1⟩
  have hnorm : Representation.norm M.ρ = LinearMap.id := by
    ext x
    rw [Representation.norm, LinearMap.sum_apply]
    have h1 : ∀ g : G, M.ρ g x = x := by
      intro g
      rw [Subsingleton.elim g 1, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ, hcard,
      one_nsmul]
    rfl
  have hker : LinearMap.ker (Representation.norm M.ρ) = ⊥ := by
    rw [hnorm, LinearMap.ker_id]
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm M.ρ)) :=
    (LinearMap.ker (Representation.norm M.ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso M.ρ
  haveI : Subsingleton (↥(LinearMap.ker (Representation.norm M.ρ)) ⧸
      Submodule.comap (LinearMap.ker (Representation.norm M.ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × M.V => M.ρ p.1 p.2 - p.2))) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
    intro z
    rw [Submodule.mem_comap]
    have hz0 : ((z : ↥(LinearMap.ker (Representation.norm M.ρ))) : M.V) = 0 := by
      have hz := z.2
      rw [LinearMap.mem_ker] at hz
      have h1 : M.ρ.norm ((z : ↥(LinearMap.ker (Representation.norm M.ρ))) : M.V) =
          ((z : ↥(LinearMap.ker (Representation.norm M.ρ))) : M.V) := by
        simpa using congrArg (fun (f : M.V →ₗ[ℤ] M.V) =>
          f ((z : ↥(LinearMap.ker (Representation.norm M.ρ))) : M.V)) hnorm
      rw [← h1]
      exact hz
    show ((z : ↥(LinearMap.ker (Representation.norm M.ρ))) : M.V) ∈ _
    rw [hz0]
    exact Submodule.zero_mem _
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- At an infinite place, the unit fibre is the fibre. -/
theorem fiberUnits_eq_fiberIdeles_ofInfinite (a : NumberField.InfinitePlace F) :
    NK.GlobalCFTdeep.fiberUnits (K := F) (L := K) (Place.ofInfinite a) =
      NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K) (Place.ofInfinite a) := by
  ext x
  rw [NK.GlobalCFTdeep.mem_fiberUnits, NK.GlobalCFTdeep.mem_fiberIdeles]
  constructor
  · intro h; exact h.1
  · intro h
    refine ⟨h, fun w => ?_⟩
    by_cases hw : Place.LiesOver w (Place.ofInfinite a)
    · rcases w with w' | q
      · exact Place.mem_localUnits_ofInfinite
      · rcases hw with ⟨u, v, h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
        · exact absurd h1 (Place.ofInfinite_ne_ofFinite u q).symm
        · exact absurd h2 (Place.ofInfinite_ne_ofFinite a Q')
    · rw [h w hw]; exact one_mem _

/-- At an infinite place, the idèles supported on the fibre are already unit idèles. -/
theorem fiberIdeles_le_fiberUnits_ofInfinite (a : NumberField.InfinitePlace F) :
    NK.GlobalCFTdeep.fiberIdeles (K := F) (L := K) (Place.ofInfinite a) ≤
      NK.GlobalCFTdeep.fiberUnits (K := F) (L := K) (Place.ofInfinite a) := by
  intro x hx
  rw [NK.GlobalCFTdeep.mem_fiberUnits]
  refine ⟨NK.GlobalCFTdeep.mem_fiberIdeles.mp hx, fun w => ?_⟩
  by_cases hw : Place.LiesOver w (Place.ofInfinite a)
  · rcases w with w' | q
    · exact Place.mem_localUnits_ofInfinite
    · rcases hw with ⟨u, v, h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite u q).symm
      · exact absurd h2 (Place.ofInfinite_ne_ofFinite a Q')
  · rw [NK.GlobalCFTdeep.mem_fiberIdeles.mp hx w hw]; exact one_mem _

/-- **The fibre at a place of `F` has vanishing `Ĥ⁻¹` for an unramified extension.** -/
theorem fiberIdelesRep_subsingleton_of_isUnramified (hunr : _root_.CFTLib.IsUnramified F K)
    (v : Place F) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberIdelesRep (K := F) (L := K) v) (-1)) := by
  rcases v with a | Q
  · obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace K, w.comap (algebraMap F K) = a :=
      NumberField.InfinitePlace.comap_surjective a
    have hwl : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite a) :=
      Place.liesOver_ofInfinite
        ((NK.GlobalCFT.Norm.liesOver_iff_comap_eq (K := F) (L := K) w a).mpr hw)
    haveI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (Place.ofInfinite w)) := Fintype.ofFinite _
    haveI : w.LiesOver a :=
      (NK.GlobalCFT.Norm.liesOver_iff_comap_eq (K := F) (L := K) w a).mpr hw
    have hunr_inf : NumberField.InfinitePlace.IsUnramified F w :=
      IsUnramifiedAtInfinitePlaces.isUnramified (self := hunr.2) w
    have hcard : Nat.card ↥(NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (Place.ofInfinite w)) = 1 := by
      rw [NK.GlobalCFTdeep.Herbrand.natCard_decompositionSubgroup_ofInfinite_eq_finrank a w,
        hunr_inf.finrank_eq_one a]
    haveI : Subsingleton ↥(NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (Place.ofInfinite w)) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact subsingleton_tateCohomology_neg_one_fiberIdelesRep_of_local (K := F) (L := K)
      (Place.ofInfinite a) (Place.ofInfinite w) hwl
      (subsingleton_tateCohomology_neg_one_of_subsingleton_group _)
  · obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := F) (L := K) Q
    have hwl : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q) := Place.liesOver_ofFinite hq
    haveI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
        (Place.ofFinite q)) := Fintype.ofFinite _
    exact subsingleton_tateCohomology_neg_one_fiberIdelesRep_of_local (K := F) (L := K)
      (Place.ofFinite Q) (Place.ofFinite q) hwl
      (subsingleton_tateCohomology_neg_one_localUnitsRep_of_ramificationIdx_eq_one Q q hq
        (ramificationIdx_eq_one_of_differentIdeal_eq_top (K := F) (L := K) hunr.1 q))

/-- **The unit fibre at a finite place of `F` has vanishing `Ĥ⁻¹` for an unramified
extension.** -/
theorem fiberUnitsRep_subsingleton_of_isUnramified
    (hunr : _root_.CFTLib.IsUnramified F K) (v : Place F) (hv : Place.IsFinite v) :
    Subsingleton (tateCohomology
      (NK.GlobalCFTdeep.fiberUnitsRep (K := F) (L := K) v) (-1)) := by
  obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp hv
  obtain ⟨q, hq⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := F) (L := K) Q
  have hwl : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q) := Place.liesOver_ofFinite hq
  haveI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (Place.ofFinite q)) := Fintype.ofFinite _
  haveI : IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := F) (L := K)
      (Place.ofFinite q)) :=
    isCyclic_decompositionSubgroup_of_ramificationIdx_eq_one Q q hq
      (ramificationIdx_eq_one_of_differentIdeal_eq_top (K := F) (L := K) hunr.1 q)
  exact subsingleton_tateCohomology_neg_one_fiberUnitsRep_of_local (K := F) (L := K)
    (Place.ofFinite Q) q hwl
    (localUnitSubRep_tateCohomology_neg_one_of_ramificationIdx_eq_one Q q hq
      (ramificationIdx_eq_one_of_differentIdeal_eq_top (K := F) (L := K) hunr.1 q))

end Final

/-- **Step 1 of Roquette's computation.**  For a finite Galois extension `K/F` of number fields
which is unramified at every place, the `(-1)`-st Tate cohomology of the idèle group `𝕀_K`
vanishes. -/
theorem tateCohomology_neg_one_idele_of_isUnramified (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (hunr : _root_.CFTLib.IsUnramified F K) :
    Subsingleton (tateCohomology (NK.CFTLib.ideleRep F K) (-1)) :=
  subsingleton_tateCohomology_neg_one_ideleRep_of_fibers (F := F) (K := K)
    (fun v => fiberIdelesRep_subsingleton_of_isUnramified (F := F) (K := K) hunr v)
    (fun v hv => fiberUnitsRep_subsingleton_of_isUnramified (F := F) (K := K) hunr v hv)

end NK.CFTLib
