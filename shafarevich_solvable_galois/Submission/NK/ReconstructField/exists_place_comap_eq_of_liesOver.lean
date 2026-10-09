import Mathlib
import Submission.NK.ReconstructField.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

set_option linter.unusedVariables false

/-- **A place of `K₁'` over `𝔭` whose image under the local correspondence restricts to a
prescribed prime `Q` of a corresponding level.**

Let `L ⊆ K₁'` be a finite normal level over `K₁` and `Q` a prime of `𝓞(levelMap ϕ L)` lying over
`a.primeMap 𝔭`.  Then there is a place `A` of `K₁'` over `𝔭` such that the place `a.placeMap A`
of `K₂'` restricts to `Q` at the level `levelMap ϕ L`.

The place is produced by extension of the local prime `Q` to `K₂'` and transport back along the
bijection `a.placeMap` of the place systems; the compatibility of the induced map on primes
(`a.primeMap_spec`) is what identifies the prime below it as `𝔭`. -/
theorem exists_place_comap_eq_of_liesOver
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁)
    (Q : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ L))
    (hQ : Q.asIdeal.LiesOver (a.primeMap 𝔭).asIdeal) :
    ∃ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      A.1.comap (algebraMap K₁ K₁') =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭 ∧
        NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
            (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2
              (NK.Reconstruct.levelMap ϕ L)) = Q := by
  -- extend the prime `Q` of the level to a place of `K₂'`
  obtain ⟨B, hB⟩ := NK.Reconstruct.exists_place_of_prime_level (K' := K₂') (k := K₂)
      (NK.Reconstruct.levelMap ϕ L) Q
  -- the algebra maps of the tower `K₂ ⊆ levelMap ϕ L ⊆ K₂'` compose
  have hcomp : (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂').comp
      (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L)) = algebraMap K₂ K₂' :=
    IsScalarTower.algebraMap_eq K₂ ↥(NK.Reconstruct.levelMap ϕ L) K₂'
  -- the prime of `𝓞 K₂` below `B` is the prime below `Q`, namely `a.primeMap 𝔭`
  have hBcomap : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ (a.primeMap 𝔭) := by
    rw [← hcomp, ← ValuationSubring.comap_comap B
        (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂')
        (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L)), hB,
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (a.primeMap 𝔭) Q hQ]
  -- in particular `B` restricts to a proper place of `K₂`
  have hBne : B.comap (algebraMap K₂ K₂') ≠ ⊤ := by
    rw [hBcomap]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := K₂) (a.primeMap 𝔭)
  let B' : NK.Reconstruct.FinitePlaceOf K₂ K₂' := ⟨B, hBne⟩
  -- the prime of `𝓞 K₂` below `B'` is `a.primeMap 𝔭`
  have hprimeB : Submission.NeukirchUchida.primeOf B'.1 B'.2 = a.primeMap 𝔭 := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₂)
    rw [← Submission.NeukirchUchida.primeOf_spec B'.1 B'.2]
    exact hBcomap
  -- transport back along the bijection of place systems
  let A : NK.Reconstruct.FinitePlaceOf K₁ K₁' := a.placeMap.symm B'
  have hmapA : a.placeMap A = B' := Equiv.apply_symm_apply a.placeMap B'
  -- the prime below `A` is `𝔭`, by coherence of `primeMap` (`a.primeMap_spec`)
  have hprimeA : Submission.NeukirchUchida.primeOf A.1 A.2 = 𝔭 := by
    apply a.primeMap.injective
    rw [a.primeMap_spec A, hmapA, hprimeB]
  refine ⟨A, ?_, ?_⟩
  · rw [Submission.NeukirchUchida.primeOf_spec A.1 A.2, hprimeA]
  · -- the level prime of the image place is `Q`, since the two valuation subrings agree
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (K := ↥(NK.Reconstruct.levelMap ϕ L))
    rw [← NK.Reconstruct.primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)),
      hmapA, hB]

end NK.ReconstructField
