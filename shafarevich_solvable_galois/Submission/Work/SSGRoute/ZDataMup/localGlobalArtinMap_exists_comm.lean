import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinSetup
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux4
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The glued local-global Artin map for a *commutative* abelian extension

`NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` produces, for a **cyclic** extension `L/K`, the
map `Φ : 𝕀_K →* Gal(L/K)` which is surjective, kills the idèlic norms, is one-place faithful, and is
Frobenius-normalised at every unramified prime.  The cyclicity hypothesis is used *only* to obtain
the commutativity of `Gal(L/K)`: `exists_localMap_ofFinite`
(`Submission/NK/CFTLib/IdeleHasse/exists_localMap_ofFinite.lean`, lines 204-206) does
`haveI := hcyc` and then derives `hcomm` and uses only `hcomm`, and
`exists_localGlobalArtinMap'` (`localGlobalArtinSetup.lean`, lines 262-284) likewise converts
`hcyc` into `hcomm`.

Hence the same construction works verbatim with a commutativity hypothesis, which is what the
result below records.  This is the natural tool for the cyclotomic case (`Gal(K(ζ_n)/K)` is
commutative but usually not cyclic), and it is *not* the conductor-drop crux: the hard clause
(`Φ` kills the principal idèles `Kˣ`) is deliberately absent.

The proof copies `NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap_aux` with `hcyc` replaced by
`hcomm`, using the abelian local Artin map at the finite places
(`Work.SSGRoute.ZDataMup.exists_localMap_ofFinite_of_abelian`) and the archimedean local map
`NK.CFTLib.IdeleHasse.exists_localMap_ofInfinite_noCyc` (which never used cyclicity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT
open NK.CFTLib.IdeleHasse

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The gluing step**, with the cyclicity hypothesis of
`NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap_aux` replaced by commutativity. -/
theorem exists_localGlobalArtinMap_aux_comm
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hw : ∀ w : InfinitePlace K, ∃ F : (w.Completion)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = localNormSubgroup (K := K) (L := L) (Place.ofInfinite w)) :
    ∃ Φ : Idele K →* (L ≃ₐ[K] L), Function.Surjective Φ ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      (∀ (v : Place K) (a : (Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  let Ffin : (Q : HeightOneSpectrum (𝓞 K)) → (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    fun Q => Classical.choose
      (Work.SSGRoute.ZDataMup.exists_localMap_ofFinite_of_abelian (K := K) (L := L) hcomm Q)
  have hFfin_ker : ∀ Q, MonoidHom.ker (Ffin Q) =
      localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) :=
    fun Q => (Classical.choose_spec
      (Work.SSGRoute.ZDataMup.exists_localMap_ofFinite_of_abelian (K := K) (L := L) hcomm Q)).1
  have hFfin_unif : ∀ (Q : HeightOneSpectrum (𝓞 K))
      (hu : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q),
      Ffin Q (IdeleClassGroup.unifUnit K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q :=
    fun Q hu => (Classical.choose_spec
      (Work.SSGRoute.ZDataMup.exists_localMap_ofFinite_of_abelian (K := K) (L := L) hcomm Q)).2 hu
  let Finf : (w : InfinitePlace K) → (w.Completion)ˣ →* (L ≃ₐ[K] L) :=
    fun w => Classical.choose (hw w)
  have hFinf_ker : ∀ w, MonoidHom.ker (Finf w) =
      localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) :=
    fun w => Classical.choose_spec (hw w)
  let F : ∀ v : Place K, (Place.localField K v)ˣ →* (L ≃ₐ[K] L) := fun v =>
    match v with
    | Sum.inl w => Finf w
    | Sum.inr Q => Ffin Q
  have hF_ker : ∀ v : Place K, MonoidHom.ker (F v) =
      localNormSubgroup (K := K) (L := L) v := by
    intro v; cases v with
    | inl w => exact hFinf_ker w
    | inr Q => exact hFfin_ker Q
  have hF_ker_apply : ∀ (v : Place K) (a : (Place.localField K v)ˣ), F v a = 1 ↔
      a ∈ localNormSubgroup (K := K) (L := L) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hF_ker v]
  have hsupport : ∀ y : Idele K, {v : Place K | F v (y v) ≠ 1}.Finite := by
    intro y
    have hInf : ({v : Place K | Place.IsInfinite v} : Set (Place K)).Finite := by
      refine (Finset.finite_toSet (Finset.univ.image (Place.ofInfinite (K := K)))).subset ?_
      intro v hv
      obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp hv
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ w))
    have hNu : ({v : Place K | y v ∉ Place.localUnits K v} : Set (Place K)).Finite :=
      Filter.eventually_cofinite.mp y.2
    have hRam : ({v : Place K | ∃ q : HeightOneSpectrum (𝓞 L),
        q.asIdeal.ramificationIdx (𝓞 K) ≠ 1 ∧
          NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q) = v}
        : Set (Place K)).Finite := by
      have hq := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)
      refine (hq.image (fun q : HeightOneSpectrum (𝓞 L) =>
        NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q))).subset ?_
      rintro v ⟨q, hqe, hqeq⟩
      exact ⟨q, hqe, hqeq⟩
    refine Set.Finite.subset (hInf.union (hNu.union hRam)) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hnot
    push_neg at hnot
    obtain ⟨h1, h2, h3⟩ := hnot
    obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp h1
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
      intro q hq
      by_contra hqe
      exact h3 q hqe
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver
          (Place.liesOver_ofFinite hq))
    exact hv ((hF_ker_apply (Place.ofFinite Q) (y (Place.ofFinite Q))).mpr
      (localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L) Q hunr h2))
  let Φ : Idele K →* (L ≃ₐ[K] L) := ideleHomOfLocal hcomm F hsupport
  have hΦ : ∀ y : Idele K, Φ y = cprod hcomm (hsupport y).toFinset (fun v => F v (y v)) := by
    intro y
    dsimp only [Φ]
    rw [ideleHomOfLocal_apply]
  have hΦ_onePlace : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = F v a := by
    intro v a
    exact ideleHomOfLocal_apply_onePlace hcomm F hsupport v a
  have h4 : ∀ (Q : HeightOneSpectrum (𝓞 K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hunr
    rw [hΦ]
    have hsingle := cprod_eq_single (hcomm := hcomm)
      (s := (hsupport (NK.HeckeL.ideleOfPrime K Q)).toFinset)
      (f := fun v => F v ((NK.HeckeL.ideleOfPrime K Q) v)) (Place.ofFinite Q)
      (fun b _ hb => by
        cases b with
        | inl w => rw [ideleOfPrime_apply_ofInfinite, map_one]
        | inr q =>
            have hqQ : q ≠ Q := fun h => hb (by rw [h])
            rw [ideleOfPrime_apply_ofFinite_ne_exists hqQ, map_one])
      (fun hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))
    rw [hsingle, ideleOfPrime_apply_ofFinite_self]
    exact hFfin_unif Q hunr
  have h1 : ∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hΦ]
    refine cprod_eq_one hcomm fun v _ => ?_
    rw [Idele.normIdeleHom_apply]
    exact (hF_ker_apply v _).mpr (normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y v)
  have h3' : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L := by
    intro v a
    rw [hΦ_onePlace v a, hF_ker_apply v a]
    exact (onePlace_mem_normImage_iff (K := K) (L := L) v a).symm
  have h2 : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top]
    let T : Finset (HeightOneSpectrum (𝓞 K)) :=
      ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)).toFinset.image (fun q : HeightOneSpectrum (𝓞 L) =>
          HeightOneSpectrum.under (𝓞 K) q))
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L) T
      Φ.range ?_
    intro p hp σ hσ
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
      intro q hq
      by_contra hqe
      have hmem : p ∈ T := by
        refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
        · rw [Set.Finite.mem_toFinset]; exact hqe
        · exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])
      exact hp hmem
    rw [NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ] at hσ
    exact ⟨NK.HeckeL.ideleOfPrime K p, by rw [h4 p hunr, hσ]⟩
  exact ⟨Φ, h2, h1, h3', h4⟩

/-- **The glued local-global Artin map for an abelian extension**: for `L/K` finite Galois with
commutative `Gal(L/K)` there is `Φ : 𝕀_K →* Gal(L/K)` which is surjective, kills the idèlic norms
`N_{L/K}𝕀_L`, is faithful at every place, and is Frobenius-normalised at every unramified prime. -/
theorem localGlobalArtinMap_exists_comm
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    ∃ Φ : NK.GlobalCFT.Idele K →* Gal(L/K), Function.Surjective Φ ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :=
  exists_localGlobalArtinMap_aux_comm hcomm
    (fun w => NK.CFTLib.IdeleHasse.exists_localMap_ofInfinite_noCyc (K := K) (L := L) w)

end Work.SSGRoute.ZDataMup
