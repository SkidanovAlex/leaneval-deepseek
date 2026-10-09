import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.TowerTransport
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.ArtinMapUniqueAbelian
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.galois_sup_structure
import Submission.Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.style.haveILetI false

/-- **Tower compatibility of the local factor of the abelian Artin map.**

If an automorphism `σ` of `Ω` over `↥K` restricts on a level `M/↥K` to the local factor
`θ^M_A(ν) = ΦM(onePlace_𝔭(localImageAt_𝔭 ν))` of an abelian idèlic Artin map `ΦM` of `M` pinned by
its kernel and its Frobenius normalisation, then its restriction to any sublevel `L ≤ M` is the
corresponding local factor `θ^L_A(ν)` of any abelian Artin map `ΦL` of `L/↥K` with the same
normalisation.  The proof reduces to the pointwise compatibility
`Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq` of the two local factors under the
inclusion `↥L ⊆ ↥M` (Chebotarev plus the relation `restrictMol` between the two restriction
maps). -/
theorem hLocalFactor_tower (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L M : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M] (hLM : L ≤ M)
    (hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a)
    (ΦM : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hΦMker : ΦM.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦMfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) Q →
      ΦM (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) Q)
    (ΦL : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΦLker : ΦL.ker = NK.GlobalCFT.Idele.normImage ↥K ↥L ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦLfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) Q →
      ΦL (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q)
    (ν : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω)
    (hσ : σ.restrictNormal M =
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA M ΦM ν) :
    σ.restrictNormal L =
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L ΦL ν := by
  classical
  haveI hNL : Normal ↥K ↥L := IsGalois.to_normal
  haveI hNM : Normal ↥K ↥M := IsGalois.to_normal
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  calc
    ((σ.restrictNormal L) x : Ω)
        = ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) σ x : Ω) := rfl
    _ = (σ (x : Ω) : Ω) := AlgEquiv.restrictNormalHom_apply L σ x
    _ = ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M) σ
          ⟨(x : Ω), hLM x.2⟩ : Ω) :=
        (AlgEquiv.restrictNormalHom_apply M σ ⟨(x : Ω), hLM x.2⟩).symm
    _ = ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA M ΦM ν)
          ⟨(x : Ω), hLM x.2⟩ : Ω) := by
        rw [show (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M) σ
            = σ.restrictNormal M from rfl, hσ]
    _ = ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L ΦL ν) x : Ω) :=
        Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq (p := p) (k := k)
          (Ω := Ω) (K := K) A hA L M hLM hcommM ΦM hΦMker hΦMfrob ΦL hΦLker hΦLfrob ν x

end Work.SSGRoute.ZDataMup.LTRecFamHonest
