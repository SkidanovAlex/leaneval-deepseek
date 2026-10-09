import Mathlib
import Submission.NK.ReconstructField.LevelPrime
import Submission.NeukirchUchida.Local.PlaceFromValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-level prime correspondence preserves the prime below

The induced map on primes of a finite level, `NK.ReconstructField.levelPrimeMap`, is defined by
choosing a place `A` of `K₁'` above a prime `P` of a finite level `L ⊆ K₁'` and taking the prime
below the corresponding place `a.placeMap A` in the corresponding level `levelMap ϕ L`.

This file verifies that this map is *compatible with the prime correspondence of the base fields*:
if `P` lies over the prime `𝔭` of `K₁`, then `levelPrimeMap ϕ hϕ a L P` lies over `a.primeMap 𝔭`.

The argument is in two steps.

* First, the place `A` above `P` has trace on `K₁` equal to the valuation ring `𝒪_𝔭` of `𝔭`:
  the trace on `K₁` is the trace on `L` of the trace on `↥L`, and the latter is
  `𝒪_{L,P}`, whose trace on `K₁` is `𝒪_𝔭` because `P` lies over `𝔭`
  (`Commons.RingTheory.Valuation.comap_valuationSubringAtPrime`).  Hence
  `Submission.NeukirchUchida.primeOf A.1 A.2 = 𝔭`, and by `LocalCorrespondence.primeMap_spec`
  applied to `A` the prime `a.primeMap 𝔭` is the prime of `K₂` below `a.placeMap A`.

* Second, the prime `primeOfLevel (a.placeMap A).1 (levelMap ϕ L) _` cut out by the place
  `a.placeMap A` on the corresponding level is the finite place induced by `a.placeMap A`
  (`Submission.NeukirchUchida.Local.placeOf`), and the latter lies over the prime below
  `a.placeMap A` (`Submission.NeukirchUchida.Local.placeOf_liesOver`).
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open scoped Pointwise

theorem levelPrimeMap_liesOver
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁) (P : NK.Chebotarev.PrimeIdeal ↥L)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.LiesOver
      (a.primeMap 𝔭).asIdeal := by
  -- a place `A` of `K₁'` above the prime `P` of the level
  obtain ⟨A, hA⟩ :=
    NK.ReconstructField.exists_finitePlace_of_prime_level (K₁ := K₁) (K₁' := K₁') L P
  -- the trace of `A` on `K₁` is the trace of the trace on `L`, which is `𝒪_𝔭` because `P` lies
  -- over `𝔭`
  have hcomp : A.1.comap (algebraMap K₁ K₁') =
      (A.1.comap (algebraMap ↥L K₁')).comap (algebraMap K₁ ↥L) := by
    refine SetLike.ext fun x => ?_
    simp only [ValuationSubring.mem_comap]
    rw [IsScalarTower.algebraMap_apply K₁ ↥L K₁']
  have hcomap : A.1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭 := by
    rw [hcomp, hA, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔭 P hP]
  -- hence the prime of `𝓞 K₁` below `A` is `𝔭`
  have hprime : Submission.NeukirchUchida.primeOf A.1 A.2 = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁) (by
      rw [← Submission.NeukirchUchida.primeOf_spec A.1 A.2, hcomap])
  -- unfold `levelPrimeMap` at the chosen place `A` and identify `a.primeMap 𝔭` with the prime
  -- below the corresponding place `a.placeMap A`
  rw [NK.ReconstructField.levelPrimeMap_spec ϕ hϕ a L P A hA, ← hprime, a.primeMap_spec A]
  -- the prime cut out by `a.placeMap A` on the corresponding level is the induced finite place
  have hkey : NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
      (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) =
      Submission.NeukirchUchida.Local.placeOf
        (Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2)
        (a.placeMap A).1
        (Submission.NeukirchUchida.primeOf_spec (a.placeMap A).1 (a.placeMap A).2)
        (NK.Reconstruct.levelMap ϕ L) := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (K := ↥(NK.Reconstruct.levelMap ϕ L)) ?_
    rw [← NK.Reconstruct.primeOfLevel_spec,
      ← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf]
  rw [hkey]
  exact Submission.NeukirchUchida.Local.placeOf_liesOver _ _ _ _

end NK.ReconstructField
