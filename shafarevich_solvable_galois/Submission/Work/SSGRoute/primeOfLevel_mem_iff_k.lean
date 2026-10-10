import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute

/-- **Description of the prime of `𝓞 M` below a finite place of `Ω` by a valuation inequality.**

Let `k` be a number field, `Ω / k` a separable closure of `k`, `B` a finite place of `Ω` (a
valuation subring whose restriction to `k` is proper) and `M ⊆ Ω` a finite extension of `k`.
Then the prime of `𝓞 M` below `B` consists precisely of the elements `x` whose image in `Ω` has
`B`-adic value `< 1`.  This is the general form (arbitrary number field `k`, arbitrary separable
closure `Ω`) of the corresponding statement for `ℚ ⊆ ℚ̄`. -/
theorem primeOfLevel_mem_iff_k (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (M : IntermediateField k Ω) [FiniteDimensional k M] (x : NumberField.RingOfIntegers ↥M) :
    x ∈ (NK.Reconstruct.primeOfLevel B M (NK.Reconstruct.comap_level_ne_top hB M)).asIdeal ↔
      B.valuation (algebraMap (NumberField.RingOfIntegers ↥M) Ω x) < 1 := by
  haveI : NumberField ↥M := NumberField.of_module_finite k ↥M
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M) :=
    NK.Reconstruct.primeOfLevel B M (NK.Reconstruct.comap_level_ne_top hB M) with hPdef
  have hspec : B.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P :=
    NK.Reconstruct.primeOfLevel_spec B M (NK.Reconstruct.comap_level_ne_top hB M)
  show x ∈ P.asIdeal ↔ _
  haveI : IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) P.asIdeal :=
    inferInstanceAs (IsLocalization P.asIdeal.primeCompl _)
  have h1 : x ∈ P.asIdeal ↔
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).valuation
        (algebraMap (NumberField.RingOfIntegers ↥M) ↥M x) < 1 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P) P.asIdeal x]
    exact ValuationSubring.valuation_lt_one_iff _ _
  rw [h1, ← hspec, comap_valuation_lt_one_iff]
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M Ω]

end Work.SSGRoute
