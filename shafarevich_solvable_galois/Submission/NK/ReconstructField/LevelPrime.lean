import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.ReconstructField.exists_finitePlace_of_prime_level
import Submission.NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The prime correspondence at finite levels

This file packages the *induced correspondence of primes at finite levels* of CoNF XII §12.2: for a
finite level `L ⊆ K₁'` (a finite normal extension of a number field `K₁`, hence a number field) with
corresponding level `levelMap ϕ L ⊆ K₂'`, the local correspondence `a` of `ϕ` induces a map

`levelPrimeMap ϕ hϕ a L : PrimeIdeal ↥L → PrimeIdeal ↥(levelMap ϕ L)`

taking a prime `P` of `𝓞 L` to the prime of the corresponding level which is the image of `P` under
the place correspondence.

**Well-definedness** is the content of the file `primeOfLevel_placeMap_eq_of_comap_eq` (two places
of `K₁'` with the same trace on the level `L` have images with the same trace on the corresponding
level `levelMap ϕ L`): this is the statement that the fibres of the place system over a level prime
are torsors under the *matching* open subgroups, which is the technical heart of the finite-level
prime correspondence.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The prime of the corresponding level attached to a prime of a finite level.**  Choose a finite
place `A` of `K₁'` above `P` (which exists by `NK.ReconstructField.exists_finitePlace_of_prime_level`)
and take the prime below the corresponding place `a.placeMap A` of `K₂'` in the corresponding level
`levelMap ϕ L`.

The value does not depend on the choice of `A`, by
`NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq` (see
`NK.ReconstructField.levelPrimeMap_spec`). -/
noncomputable def levelPrimeMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L) : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ L) :=
  NK.Reconstruct.primeOfLevel
    (a.placeMap (exists_finitePlace_of_prime_level L P).choose).1
    (NK.Reconstruct.levelMap ϕ L)
    (NK.Reconstruct.comap_level_ne_top
      (a.placeMap (exists_finitePlace_of_prime_level L P).choose).2
      (NK.Reconstruct.levelMap ϕ L))

/-- **The computation rule of `levelPrimeMap`**: the induced prime does not depend on the choice of
a place of `K₁'` above `P`.  This is the well-definedness of the finite-level prime correspondence:
the image of the place `A` under `a.placeMap` cuts out on the corresponding level exactly the prime
`levelPrimeMap ϕ hϕ a L P`. -/
theorem levelPrimeMap_spec (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L)
    (A : NK.Reconstruct.FinitePlaceOf K₁ K₁')
    (hA : A.1.comap (algebraMap ↥L K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P) :
    levelPrimeMap ϕ hϕ a L P =
      NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2
          (NK.Reconstruct.levelMap ϕ L)) := by
  unfold levelPrimeMap
  exact primeOfLevel_placeMap_eq_of_comap_eq ϕ hϕ a L _ A (by
    rw [(exists_finitePlace_of_prime_level L P).choose_spec, hA])

end NK.ReconstructField
