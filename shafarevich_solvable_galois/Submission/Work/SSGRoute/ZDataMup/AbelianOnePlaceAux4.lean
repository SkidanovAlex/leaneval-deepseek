import Mathlib
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute
import Submission.NK.LocalReciprocity.ArtinUnramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Artin map at a finite place, for an abelian extension

`exists_localMap_ofFinite` produces, for a **cyclic** extension `L/K` and a finite place `Q`, a
homomorphism `(K_Q)ˣ →* Gal(L/K)` whose kernel is the local norm subgroup `N_L(Q)`.  Its proof
uses only the commutativity of `Gal(L/K)`, so it applies verbatim to every finite **abelian**
extension; this module records that form, which is the local building block of the abelian
one-place theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT
open NK.CFTLib.IdeleHasse

namespace Work.SSGRoute.ZDataMup

/-- **The local Artin map of an abelian extension at a finite place.** -/
theorem exists_localMap_ofFinite_of_abelian {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ F : (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) ∧
      (NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        F (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) =
          NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  by_cases hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q
  · have hu : q.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr q hq
    refine ⟨(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
        (K := K) q).subtype.comp
      ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
          Q q hq).symm.toMonoidHom.comp
        (NK.LocalReciprocity.artinUnramified Q q hu)), ?_, ?_⟩
    · refine ker_comp_decompositionSubgroupMulEquivLocalGalois Q q _ ?_
      rw [NK.LocalReciprocity.ker_artinUnramified Q q hu]
      rfl
    · intro _
      have hval : NK.LocalReciprocity.artinUnramified Q q hu
          (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) =
          NK.LocalReciprocity.frobeniusLocal Q q hu := by
        rw [NK.LocalReciprocity.artinUnramified_apply, NK.LocalReciprocity.valExponent_apply,
          NK.GlobalCFT.IdeleClassGroup.valued_unifUnit, WithZero.log_exp]
        simp
      have hψ : Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun Q q hq
          ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
            Q q hq).symm (NK.LocalReciprocity.frobeniusLocal Q q hu))
          = NK.LocalReciprocity.frobeniusLocal Q q hu := by
        have hcoee :=
          Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
            Q q hq ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
              Q q hq).symm (NK.LocalReciprocity.frobeniusLocal Q q hu))
        rw [MulEquiv.apply_symm_apply] at hcoee
        exact hcoee.symm
      have hfrob : NK.Chebotarev.IsFrobAt q
          ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
            Q q hq).symm (NK.LocalReciprocity.frobeniusLocal Q q hu)).1 :=
        isFrobAt_of_decompositionToLocalGalois_eq_frobeniusLocal Q q hu _ _ hψ
      have hfp : NK.Chebotarev.frobAtPrime (K := K) (L := L) Q
          = ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
              Q q hq).symm (NK.LocalReciprocity.frobeniusLocal Q q hu)).1 :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm Q hunr _).mp ⟨q, hq, hfrob⟩
      rw [hfp]
      show ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
          Q q hq).symm (NK.LocalReciprocity.artinUnramified Q q hu
            (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q))).1
        = ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
            Q q hq).symm (NK.LocalReciprocity.frobeniusLocal Q q hu)).1
      rw [hval]
  · obtain ⟨Φ, _, hΦker⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute hcomm Q q hq
    refine ⟨(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
        (K := K) q).subtype.comp
      ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
          Q q hq).symm.toMonoidHom.comp Φ), ?_, ?_⟩
    · refine ker_comp_decompositionSubgroupMulEquivLocalGalois Q q Φ ?_
      rw [hΦker]
      rfl
    · intro hbad
      exact absurd hbad hunr

end Work.SSGRoute.ZDataMup
