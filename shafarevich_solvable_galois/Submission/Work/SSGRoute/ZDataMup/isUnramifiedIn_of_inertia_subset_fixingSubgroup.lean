import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupOddAux
import Submission.Work.SSGRoute.mem_levelSub_iff_mem_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-- **A private copy of `Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn`**
(the statement is not changed, only its proof is repeated here) so that this module does not have to
import `Work.SSGRoute.shafarevich_theorem13`, whose cone contains a module that re-declares
`Work.SSGRoute.ZDataMup.exists_cocycle_of_lcHoms` — importing it here would break the shared build
with a duplicate-declaration error (`mupH1locLcHoms` is in this module's closure through
`mupOddAux`). -/
private theorem ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn'
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunr : ¬ SSGRoute.IsRamifiedIn k L A) :
    (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 := by
  classical
  haveI hNumL : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hNormL : Normal k ↥L := inferInstance
  have hker : Work.SSGRoute.inertiaSub k Ω A ≤ (AlgEquiv.restrictNormalHom L).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    rw [show AlgEquiv.restrictNormalHom L σ = σ.restrictNormal ↥L from rfl,
      AlgEquiv.restrictNormal_eq_one_iff]
    intro x hx
    by_contra hne
    exact hunr ⟨σ, (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ,
      fun hmem => hne ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hmem x hx)⟩
  have hbot : Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal = ⊥ := by
    have hlev : Work.SSGRoute.levelInertiaOf k Ω A hA L = ⊥ := by
      rw [← Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L,
        Subgroup.map_eq_bot_iff]
      exact hker
    simpa only [Work.SSGRoute.levelInertiaOf, Work.SSGRoute.levelPrimeOf] using hlev
  haveI hPprime : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.IsPrime :=
    (Work.SSGRoute.levelPrime k Ω A hA L).isPrime
  exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    ((Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.under (NumberField.RingOfIntegers k))
    (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal).mp hbot

theorem isUnramifiedIn_of_inertia_subset_fixingSubgroup {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsSepClosure K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] [NumberField ↥L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : ∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace K B →
        B.comap (algebraMap K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 →
        ∀ σ : Ω ≃ₐ[K] Ω, SSGRoute.IsInertia K B σ → σ ∈ L.fixingSubgroup) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := ↥L) 𝔭 := by
  -- `IsUnramifiedIn 𝔭` is the statement `e(𝔮/𝔭) = 1` for every prime `𝔮` of `L` over `𝔭`.
  classical
  intro 𝔮 h𝔮
  -- A place `A` of `Ω` lying over the prime `𝔮` of `L`: its valuation ring on `↥L` is the
  -- valuation ring at `𝔮`.
  obtain ⟨A, hAcomap⟩ := NK.Reconstruct.exists_place_of_prime_level (k := K) (K' := Ω) L 𝔮
  -- The valuation ring of `A` on `K` is the valuation ring at `𝔭`: restricting to `K` is the
  -- same as restricting to `↥L` and then to `K`, and `𝔮` lies over `𝔭`.
  have hcomp : A.comap (algebraMap K Ω) =
      (A.comap (algebraMap ↥L Ω)).comap (algebraMap K ↥L) := by
    have e : algebraMap K Ω = (algebraMap ↥L Ω).comp (algebraMap K ↥L) :=
      IsScalarTower.algebraMap_eq K ↥L Ω
    rw [e, ValuationSubring.comap_comap]
  have hAK : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
    rw [hcomp, hAcomap]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔭 𝔮 h𝔮
  -- so `A` is a finite place of `Ω` over `K`, and lies over `𝔭`
  have hB : SSGRoute.IsFinPlace K A := by
    show A.comap (algebraMap K Ω) ≠ ⊤
    rw [hAK]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  -- by hypothesis the inertia of `A` fixes `L`, so `𝔭` is not ramified at `A` in the sense of
  -- `SSGRoute.IsRamifiedIn`
  have hunr : ¬ SSGRoute.IsRamifiedIn K L A := by
    rintro ⟨σ, hσI, hσL⟩
    exact hσL (h A hB hAK σ hσI)
  have h1r :=
    ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn' K Ω L A hB hunr
  -- and the prime cut out on `L` by `A` is `𝔮`, since both have the same valuation ring
  have hlp : Work.SSGRoute.levelPrime K Ω A hB L = 𝔮 := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥L) (K := ↥L)
    rw [← NK.Reconstruct.primeOfLevel_spec A L (NK.Reconstruct.comap_level_ne_top hB L), hAcomap]
  rw [← hlp]
  exact h1r

end Work.SSGRoute.ZDataMup
