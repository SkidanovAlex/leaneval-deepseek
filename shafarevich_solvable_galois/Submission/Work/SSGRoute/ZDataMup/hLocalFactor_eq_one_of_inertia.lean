import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open Work.SSGRoute.ZDataMup.LTRecFamHonest

theorem hLocalFactor_eq_one_of_inertia {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    (hcard : Nat.card (↥L ≃ₐ[↥K] ↥L) = p)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L)
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA))
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΦ : ∀ x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥L, Φ x = 1) (β : (↥K)ˣ)
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k A σ →
        Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0) :
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor (K := K) A hA L Φ β = 1 := by
  refine hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA L Φ hΦ β ?_
  -- the prime of `↥K` below `A`
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    hPrimeBelow (K := K) A hA with h𝔭def
  have h𝔭spec : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    rw [h𝔭def]
    exact Submission.NeukirchUchida.primeOf_spec A
      (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA)
  -- the vanishing of the Kummer character on the inertia makes `β` a local `p`-th power times a unit
  obtain ⟨γ, u, hu, hβeq⟩ :=
    Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
      p k Ω K ζ hζ A hA 𝔭 h𝔭spec β hβ
  have hloc : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite 𝔭) β = γ ^ p * u := hβeq
  rw [hloc]
  refine mul_mem ?_ ?_
  · -- a local `p`-th power is a local norm
    exact mem_localNormSubgroup_of_mem_powRange (K := ↥K) (L := ↥L) hcard
      (NK.GlobalCFT.Place.ofFinite 𝔭) (γ ^ p) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  · -- a local unit is a local norm at an unramified place
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
      (K := ↥K) (L := ↥L) 𝔭 hunr hu

end Work.SSGRoute.ZDataMup
