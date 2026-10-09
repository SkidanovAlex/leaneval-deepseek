import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.comap_eq_of_primeOfLevel_placeMap_eq
import Submission.NK.ReconstructField.levelPrimeMap_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-level prime correspondence is a bijection

The induced correspondence of primes at finite levels (`NK.ReconstructField.levelPrimeMap`) is
injective — this is the converse of its well-definedness
(`NK.ReconstructField.comap_eq_of_primeOfLevel_placeMap_eq`: places with the same image prime have
the same trace on the level) — and surjective (`NK.ReconstructField.levelPrimeMap_surjective`,
from the surjectivity of the place map `a.placeMap`).  Hence it is a bijection, i.e. it induces a
bijection between the primes of `𝓞 L` and those of `𝓞 (levelMap ϕ L)`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The finite-level prime correspondence is injective.**  Two primes of a finite level with the
same image under `levelPrimeMap` are equal: choosing places above them, their images have the same
trace on `levelMap ϕ L`, and the converse of well-definedness
(`NK.ReconstructField.comap_eq_of_primeOfLevel_placeMap_eq`) shows that the places themselves have
the same trace on `L`. -/
theorem levelPrimeMap_injective (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    Function.Injective (levelPrimeMap ϕ hϕ a L) := by
  intro P P' h
  have hP := (exists_finitePlace_of_prime_level L P).choose_spec
  have hP' := (exists_finitePlace_of_prime_level L P').choose_spec
  have h1 : NK.Reconstruct.primeOfLevel
        (a.placeMap (exists_finitePlace_of_prime_level L P).choose).1
        (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top
          (a.placeMap (exists_finitePlace_of_prime_level L P).choose).2
          (NK.Reconstruct.levelMap ϕ L)) =
      NK.Reconstruct.primeOfLevel
        (a.placeMap (exists_finitePlace_of_prime_level L P').choose).1
        (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top
          (a.placeMap (exists_finitePlace_of_prime_level L P').choose).2
          (NK.Reconstruct.levelMap ϕ L)) := by
    rw [← levelPrimeMap_spec ϕ hϕ a L P _ hP, ← levelPrimeMap_spec ϕ hϕ a L P' _ hP', h]
  have h2 := comap_eq_of_primeOfLevel_placeMap_eq ϕ hϕ a L _ _ h1
  rw [hP, hP'] at h2
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective h2

/-- **The finite-level prime correspondence is a bijection.** -/
theorem levelPrimeMap_bijective (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    Function.Bijective (levelPrimeMap ϕ hϕ a L) :=
  ⟨levelPrimeMap_injective ϕ hϕ a L, levelPrimeMap_surjective ϕ hϕ a L⟩

end NK.ReconstructField
