import Mathlib
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective

namespace NK.ReconstructField

open scoped Pointwise

set_option linter.unusedVariables false

/-- **The finite-level prime correspondence is `Gal`-equivariant.**

The map `levelPrimeMap ϕ hϕ a L : PrimeIdeal ↥L → PrimeIdeal ↥(levelMap ϕ L)` of Neukirch–Uchida
§12.2 (the prime of the corresponding level induced by the local correspondence `a`) intertwines
the action of `Gal(K₁'/K₁)` on the primes of the level `L` with the action of `Gal(K₂'/K₂)` on the
primes of the corresponding level `levelMap ϕ L`, via the isomorphism `ϕ`:

`levelPrimeMap (g • P) = ϕ g • levelPrimeMap P`.

The proof is the standard reduction to places.  Choose a place `A` of `K₁'` above `P`; the place
`g • A` lies above `g • P` (compatibility of the Galois action on places with the restriction to
the level: `(g • A) ∩ L = g|_L • (A ∩ L)`), so `levelPrimeMap (g • P)` is computed from
`a.placeMap (g • A)`; by the equivariance `a.map_smul` of the local correspondence
`a.placeMap (g • A) = (ϕ g) • a.placeMap A`; and taking the trace on the corresponding level
commutes with the action of `Gal(K₂'/K₂)` for the same reason as before. -/
theorem levelPrimeMap_smul_of_lift
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (g : Gal(K₁'/K₁)) (P : NK.Chebotarev.PrimeIdeal ↥L) :
    NK.ReconstructField.levelPrimeMap ϕ hϕ a L
        (AlgEquiv.restrictNormalHom L g • P) =
      AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) •
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
  -- a place of `K₁'` above `P`
  obtain ⟨A, hA⟩ :=
    NK.ReconstructField.exists_finitePlace_of_prime_level (K₁ := K₁) (K₁' := K₁') L P
  -- the corresponding level and the corresponding place
  set M : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ L
  set B : NK.Reconstruct.FinitePlaceOf K₂ K₂' := a.placeMap A
  -- the place `g • A` lies above `g|_L • P`
  have hA' : (NK.Reconstruct.placeSmul g A).1.comap (algebraMap ↥L K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
        (AlgEquiv.restrictNormalHom L g • P) := by
    rw [NK.Reconstruct.placeSmul_val,
      Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A.1 g L, hA]
    exact Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      (K := K₁) (L := ↥L) P (AlgEquiv.restrictNormalHom L g • P)
      (AlgEquiv.restrictNormalHom L g) (NK.Chebotarev.smul_primeIdeal_asIdeal _ P)
  -- the two corresponding places have the same trace on the corresponding level
  have hplace : (a.placeMap (NK.Reconstruct.placeSmul g A)).1 = (ϕ g) • B.1 := by
    have h := congrArg (fun x : NK.Reconstruct.FinitePlaceOf K₂ K₂' =>
      (x : ValuationSubring K₂')) (a.map_smul g A)
    rw [NK.Reconstruct.placeSmul₂_val] at h
    exact h
  -- the value of `levelPrimeMap` at `P`
  have hP : NK.ReconstructField.levelPrimeMap ϕ hϕ a L P =
      NK.Reconstruct.primeOfLevel B.1 M (NK.Reconstruct.comap_level_ne_top B.2 M) :=
    NK.ReconstructField.levelPrimeMap_spec ϕ hϕ a L P A hA
  -- compare the valuation subrings of the two primes
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥M) ?_
  calc IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L
          (AlgEquiv.restrictNormalHom L g • P))
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
          (NK.Reconstruct.primeOfLevel (a.placeMap (NK.Reconstruct.placeSmul g A)).1 M
            (NK.Reconstruct.comap_level_ne_top
              (a.placeMap (NK.Reconstruct.placeSmul g A)).2 M)) := by
        rw [NK.ReconstructField.levelPrimeMap_spec ϕ hϕ a L _
          (NK.Reconstruct.placeSmul g A) hA']
    _ = (a.placeMap (NK.Reconstruct.placeSmul g A)).1.comap (algebraMap ↥M K₂') :=
        (NK.Reconstruct.primeOfLevel_spec _ M _).symm
    _ = ((ϕ g) • B.1).comap (algebraMap ↥M K₂') := by rw [hplace]
    _ = AlgEquiv.restrictNormalHom M (ϕ g) • (B.1.comap (algebraMap ↥M K₂')) :=
        Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul B.1 (ϕ g) M
    _ = AlgEquiv.restrictNormalHom M (ϕ g) •
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
            (NK.Reconstruct.primeOfLevel B.1 M (NK.Reconstruct.comap_level_ne_top B.2 M)) := by
        rw [NK.Reconstruct.primeOfLevel_spec B.1 M _]
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
          (AlgEquiv.restrictNormalHom M (ϕ g) •
            NK.Reconstruct.primeOfLevel B.1 M (NK.Reconstruct.comap_level_ne_top B.2 M)) :=
        Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
          (K := K₂) (L := ↥M)
          (NK.Reconstruct.primeOfLevel B.1 M (NK.Reconstruct.comap_level_ne_top B.2 M))
          (AlgEquiv.restrictNormalHom M (ϕ g) •
            NK.Reconstruct.primeOfLevel B.1 M (NK.Reconstruct.comap_level_ne_top B.2 M))
          (AlgEquiv.restrictNormalHom M (ϕ g))
          (NK.Chebotarev.smul_primeIdeal_asIdeal (AlgEquiv.restrictNormalHom M (ϕ g)) _)
    _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
          (AlgEquiv.restrictNormalHom M (ϕ g) •
            NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) := by rw [hP]

end NK.ReconstructField
