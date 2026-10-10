import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.myv2.transfer_of_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

/-- **Level compatibility of the idèlic Artin map, in the form of a restriction identity.** -/
theorem restrictNormalHom_artinMap_eq_of_le {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M E : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [FiniteDimensional ↥K E] [IsGalois ↥K E] [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)] [NumberField ↥E]
    (hME : M ≤ E)
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) Q →
      art (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) Q)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hΦker : Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) :
    ∀ (σ : Ω ≃ₐ[↥K] Ω) (x : NK.GlobalCFT.Idele ↥K),
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ = Φ x →
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ = art x := by
  intro σ x h
  -- The elementwise form of the level compatibility of the abelian Artin maps
  have hcomp := Work.SSGRoute.myv2.transfer_of_le p K M E hME art hker hfrob Φ hΦker hΦfrob
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  -- Both sides have the same image in `Ω`
  have hM : (((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) y : ↥M) : Ω) = σ (y : Ω) :=
    AlgEquiv.restrictNormalHom_apply M σ y
  have hE : (((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ)
      ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) = σ (y : Ω) :=
    AlgEquiv.restrictNormalHom_apply E σ ⟨(y : Ω), hME y.2⟩
  have hΦ : (((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) = σ (y : Ω) := by
    rw [← h]
    exact hE
  rw [hM, hcomp x y, hΦ]

end Work.SSGRoute.N2v2
