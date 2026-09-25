import Mathlib
import Submission.CFTLib.Interfaces
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.ClassFormation
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
import Submission.NK.CFTLib.indexNormClassSubgroupLeCardClassGroup

/-! Guidance from the project lead (the requester):

# Guidance: unramified abelian L/K has [L:K] ≤ h_K, from the fundamental class
Definitions: `Submission/CFTLib/Interfaces.lean` (do not edit). From `hFC`, the class-formation axioms hold
(`NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement`, `cohomologicalFieldAxiom_of_fundamentalClass`)
and reciprocity gives C_K/N_{L/K}C_L ≅ Gal(L/K) for abelian L/K (`artinReciprocity_of_cohomologicalFieldAxiom`),
so [C_K : N C_L] = [L:K]. For L/K unramified at all finite primes and real places staying real, every local unit
(and K_v^× at real v... careful: real v stays real so the local norm from ℝ is onto ℝ^× only if L_w = ℝ, which holds)
is a local norm (`norm_units_surjective_of_ramificationIdx_eq_one` in the Commons), so N C_L ⊇ image of
∏ units, and C_K/(image of units) ≅ Cl_K (ideal map of idèles; see
`NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup` for the idèle ↔ ray class
comparison). Hence [L:K] = [C_K : N C_L] ≤ h_K. Note the infinite places: a real place of K that stays real
contributes no condition; complex places have connected K_v^× = norms.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain
open NK.GlobalCFTdeep.SecondInequality.KummerCase

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-! ## Auxiliary lemmas -/

/-- If the relative different of a finite extension of number fields is the unit ideal, then every
finite prime of the extension is unramified. -/
theorem ramificationIdx_eq_one_of_differentIdeal_eq_top_of_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (q : HeightOneSpectrum (𝓞 L)) :
    q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
    (E := K) (K := L) q.asIdeal q.isPrime, h]
  intro hq
  rw [Ideal.dvd_iff_le] at hq
  exact q.isPrime.ne_top (top_le_iff.mp hq)

/-- At an infinite place the local norm is surjective if the extension is unramified at infinity:
a real place of `K` is then covered only by real places of `L`, where the local norm is the
identity, and a complex place of `K` only by complex places, where the local norm is surjective as
well. -/
theorem localNormInfinite_range_eq_top_of_isUnramifiedAtInfinitePlaces
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hinf : IsUnramifiedAtInfinitePlaces K L)
    (w : InfinitePlace L) (v : InfinitePlace K) [hw : w.LiesOver v] :
    (Place.localNormInfinite w v).range = ⊤ := by
  haveI := hinf
  rw [show Place.localNormInfinite w v =
      Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
  rcases v.isReal_or_isComplex with hv | hv
  · exact NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hv
      (NumberField.InfinitePlace.IsUnramified.liesOver_isReal_over w v
        (NumberField.InfinitePlace.isUnramified K w) hv)
  · exact NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hv
      (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hv)

/-- **The idèles which are local units at every finite place lie in the norm group** of an
unramified finite extension `L / K`.

At each place `v` of `K` choose a place `w` of `L` above it.  At a finite place the local norm on
units is surjective (`norm_units_surjective_of_ramificationIdx_eq_one`, using that the relative
different is the unit ideal), and at an infinite place the whole local norm is surjective because
real places stay real.  The idèle of `L` obtained by putting the chosen local preimage at `w` for
each `v` (and `1` elsewhere) is a genuine idèle — all its finite components are local units — and
its norm is `x`. -/
theorem integralIdeles_le_normImage
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L) :
    Idele.integralIdeles K ≤ Idele.normImage K L := by
  classical
  intro x hx
  rw [Idele.mem_normImage]
  have hxint : ∀ v : Place K, Place.IsFinite v → x v ∈ Place.localUnits K v :=
    Idele.mem_integralIdeles.mp hx
  -- ### The local data: a place of `L` above each place of `K` and a local preimage
  have hhex : ∀ v : Place K, ∃ (w : Place L) (u : (Place.localField L w)ˣ),
      Place.LiesOver w v ∧ Idele.normIdeleFun K L (singleIdele w u) v = x v ∧
        u ∈ Place.localUnits L w := by
    intro v
    cases v with
    | inl v' =>
        obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v'
        have hwl : w.LiesOver v' := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v').mpr hw
        haveI : w.LiesOver v' := hwl
        have htop := localNormInfinite_range_eq_top_of_isUnramifiedAtInfinitePlaces hinf w v'
        have hmem : x (Place.ofInfinite v') ∈ (Place.localNormInfinite w v').range := by
          rw [htop]; exact Subgroup.mem_top _
        obtain ⟨u, hu⟩ := hmem
        exact ⟨Place.ofInfinite w, u, Place.liesOver_ofInfinite hwl,
          by rw [normIdeleFun_singleIdele_ofInfinite v' w u]; exact hu,
          Place.mem_localUnits_ofInfinite⟩
    | inr Q =>
        obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
          (K := K) (L := L) Q
        have hram := ramificationIdx_eq_one_of_differentIdeal_eq_top_of_unramified hfin q
        obtain ⟨u, humem, hueq⟩ := localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q hq hram (x (Place.ofFinite Q))
          (hxint (Place.ofFinite Q) (Place.isFinite_ofFinite Q))
        exact ⟨Place.ofFinite q, u, Place.liesOver_ofFinite hq,
          by rw [normIdeleFun_singleIdele_ofFinite Q q hq u]; exact hueq, humem⟩
  choose g hval hlies hnorm hunit using hhex
  -- ### The idèle of `L` realising the local norms
  have hyeventually : ∀ᶠ w in Filter.cofinite, yValue g hval w ∈ Place.localUnits L w := by
    refine Filter.Eventually.of_forall fun w => ?_
    by_cases hex : ∃ v : Place K, g v = w
    · obtain ⟨v, hv⟩ := hex
      rw [← hv]
      exact yValue_mem_localUnits_pickW (S := ∅) (T' := ∅) hlies (fun v _ _ => hunit v)
        (by simp) (by simp)
    · push Not at hex
      rw [yValue_eq_one_of_liesOver_ne (liesOver_placeUnder w) (hex (placeUnder K L w)).symm]
      exact Subgroup.one_mem _
  let y : Idele L := ⟨yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  have hsingle : ∀ w : Place L, Place.LiesOver w v →
      y w = singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) = yValue g hval (g v) from rfl, yValue_pickW hlies v,
        singleIdele_apply_self]
    · rw [show y w = yValue g hval w from rfl, yValue_eq_one_of_liesOver_ne hw h,
        singleIdele_apply_of_ne (w' := w) h (hval v)]
  rw [← hnorm v]
  exact (normIdeleFun_congr_of_liesOver hsingle).symm


/-- The image in `C_K` of the idèles which are local units at every finite place is contained in
the norm subgroup `N_{L/K} C_L` of an unramified finite extension `L / K`. -/
theorem integralIdeles_map_le_normClassSubgroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L) :
    (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ Idele.normClassSubgroup K L := by
  change (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤
    (Idele.normImage K L).map (IdeleClassGroup.mk K)
  exact Subgroup.map_mono (integralIdeles_le_normImage hfin hinf)

/-- **Unramified abelian `L / K` has `[L : K] ≤ h_K`**, from the existence of the fundamental
class.

Artin's reciprocity isomorphism (a consequence of the fundamental class) computes
`[L : K] = [C_K : N_{L/K} C_L]`.  The norm subgroup contains the image of the local units, whose
quotient is the ideal class group; hence `[C_K : N_{L/K} C_L] ≤ h_K`. -/
theorem unramifiedAbelianDegreeLe (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    CFTLib.UnramifiedAbelianDegreeLe := by
  intro K L hK hNK hL hNL hAlg hFD hGal hcomm hunr
  haveI : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨hcomm⟩⟩
  have hrec : NK.GlobalCFT.ArtinReciprocity K L :=
    NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC
  have hidx := NK.GlobalCFT.index_normClassSubgroup_eq_finrank (K := K) (L := L) hrec
  have hbound := indexNormClassSubgroupLeCardClassGroup (K := K) (L := L)
    (integralIdeles_map_le_normClassSubgroup (K := K) (L := L) hunr.1 hunr.2)
  rw [← hidx]
  exact hbound

end NK.CFTLib
