import Mathlib
import Submission.Work.SSGRoute.ZConstruction.HFactorHelpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ZConstruction

open Work.SSGRoute.ZDataMup.LTRecFamHonest

/-- **Restriction of the chosen Frobenius to a subfield, in the `Ω`-setting.**

`L M : IntermediateField K Ω` with `L ≤ M`, both finite Galois number field extensions of the
number field `K`, `M/K` abelian, and `Q` a prime of `𝓞 K` unramified in `M/K`.  Then the
`K`-automorphism `restrictMol L M hLM` (which realises `Gal(M/K) →* Gal(L/K)` by lifting to the
normal ambient field `Ω`) carries the chosen Frobenius of `M/K` at `Q` to the chosen Frobenius of
`L/K` at `Q`.

The proof transports `L` into `M` (`hRestrict`), applies
`restrictNormalHom_frobAtPrime_of_intermediateField` there, and transports back along the bridge
`conjHom_hRestrictEquiv_restrictMol`; uniqueness of the Frobenius in the abelian extension
`↥(hRestrict L M hLM)/K` (its group is a quotient of the abelian `Gal(M/K)`) pins the answer. -/
theorem restrictMol_frobAtPrime {K : Type} {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [NumberField K] [Normal K Ω] {L M : IntermediateField K Ω} (hLM : L ≤ M)
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M]
    [NumberField ↥L] [NumberField ↥M]
    (hcommM : ∀ a b : ↥M ≃ₐ[K] ↥M, a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := ↥M) Q) :
    Work.SSGRoute.ZDataMup.LTRecFamHonest.restrictMol L M hLM
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q := by
  classical
  haveI hNL : Normal K L := IsGalois.to_normal
  haveI hNM : Normal K M := IsGalois.to_normal
  -- Transport `L ≤ M` into `↥M`, and the identification `↥(hRestrict L M hLM) ≃ₐ[K] ↥L`.
  let L' : IntermediateField K ↥M := hRestrict (K := K) L M hLM
  let e : ↥L' ≃ₐ[K] ↥L := hRestrictEquiv (K := K) L M hLM
  haveI hL'fin : FiniteDimensional K ↥L' :=
    finiteDimensional_hRestrict (K := K) (L := L) (M := M) hLM
  haveI hL'gal : IsGalois K ↥L' := isGalois_hRestrict (K := K) (L := L) (M := M) hLM
  haveI hL'nf : NumberField ↥L' := numberField_hRestrict (K := K) (L := L) (M := M) hLM
  haveI hL'norm : Normal K ↥L' := hL'gal.to_normal
  -- `Gal(L'/K)` is a quotient of the abelian group `Gal(M/K)`, hence abelian.
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L') :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L') ↥M
  have hcommL' : ∀ a b : ↥L' ≃ₐ[K] ↥L', a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul, hcommM a' b']
  -- `Q` is unramified in `L'/K` because it is unramified in `M/K`.
  have hunrL' : NK.HeckeL.IsUnramifiedIn (K := K) (L := ↥L') Q :=
    Work.SSGRoute.ZDataMup.ArtinUniqueness.isUnramifiedIn_intermediateField
      (K := K) (M := ↥M) L' Q hunr
  -- The restriction of the Frobenius of `M/K` to the transported subfield is the Frobenius of
  -- `L'/K`.
  have hrho : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L'
        (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q :=
    Work.SSGRoute.ZDataMup.ArtinUniqueness.restrictNormalHom_frobAtPrime_of_intermediateField
      (K := K) (M := ↥M) L' hcommM hcommL' Q hunr
  -- Bridge: `restrictMol` is `conjHom e` applied to the restriction to `L'`.
  have hbridge : restrictMol L M hLM (NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) Q)
      = NK.NUV2.ARL.SC.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q) := by
    rw [← hrho]
    exact (conjHom_hRestrictEquiv_restrictMol (K := K) (L := L) (M := M) hLM _).symm
  -- Uniqueness of the Frobenius at `Q` in the abelian extension `L'/K`.
  have hfrobL' : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L') Q
      (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q) :=
    NK.Chebotarev.isFrobAtPrime_frobAtPrime hcommL' Q hunrL'
  have hfrobL : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) Q
      (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q) :=
    NK.NUV2.ARL.SC.isFrobAtPrime_frobAtPrime' (K := K) (L := ↥L) Q
  -- Transport the Frobenius of `L/K` back to `L'/K` along `e.symm`: it agrees with the Frobenius
  -- of `L'/K` by uniqueness.
  have ht : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L') Q
      (NK.NUV2.ARL.SC.conjHom e.symm (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q)) :=
    (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase e.symm
      (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q) Q).mp hfrobL
  have hconj : NK.NUV2.ARL.SC.conjHom e.symm (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q :=
    (NK.Chebotarev.ExistsUniqueIsFrobAtPrime hcommL' Q hunrL').unique ht hfrobL'
  have hfinal : NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q
      = NK.NUV2.ARL.SC.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q) := by
    calc NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q
        = NK.NUV2.ARL.SC.conjHom e (NK.NUV2.ARL.SC.conjHom e.symm
            (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) Q)) :=
          (NK.NUV2.ARL.SC.conjHom_symm_conjHom e _).symm
      _ = NK.NUV2.ARL.SC.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L') Q) := by
            rw [hconj]
  rw [hbridge, ← hfinal]

end Work.SSGRoute.ZConstruction
