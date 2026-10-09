import Mathlib
import Submission.NK.Reconstruct.LevelPrimeGen
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen_gen
import Submission.NK.ReconstructField.levelPrimeMap_surjective
import Submission.NK.ReconstructField.exists_finitePlace_of_prime_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

set_option linter.unusedVariables false

/-- **The finite-level prime correspondence is a bijection, for an arbitrary finite level.**

This is `NK.ReconstructField.levelPrimeMap_bijective` with the normality hypotheses on the level
`L` (and on the corresponding level `levelMap ϕ L`) dropped.

*Injectivity* uses the general converse of well-definedness
(`NK.ReconstructField.comap_eq_of_primeOfLevel_placeMap_eq_genGen`): if two primes of `L` have the
same image prime under `levelPrimeMapGen`, then the places above them have the same trace on `L`,
so the primes themselves coincide.

*Surjectivity* is the argument of `NK.ReconstructField.levelPrimeMap_surjective`, with the
general computation rule `NK.Reconstruct.levelPrimeMapGen_spec` in place of `levelPrimeMap_spec`:
extend a prime `Q` of `levelMap ϕ L` to a finite place `B` of `K₂'`, transport it back along the
bijection `a.placeMap` of place systems to a finite place `A` of `K₁'`, and take the trace `P` of
`A` on `L`.  Then `levelPrimeMapGen ϕ hϕ a L P` is computed from the place `A` and equals the trace
of `a.placeMap A = B` on `levelMap ϕ L`, i.e. `Q`. -/
theorem levelPrimeMapGen_bijective {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    Function.Bijective (NK.ReconstructField.levelPrimeMapGen ϕ hϕ a L) := by
  constructor
  · -- injectivity
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
      rw [← levelPrimeMapGen_spec ϕ hϕ a L P _ hP,
        ← levelPrimeMapGen_spec ϕ hϕ a L P' _ hP', h]
    have h2 := comap_eq_of_primeOfLevel_placeMap_eq_genGen ϕ hϕ a L _ _ h1
    rw [hP, hP'] at h2
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective h2
  · -- surjectivity
    intro Q
    -- extend `Q` to a finite place of `K₂'`
    obtain ⟨B, hB⟩ := exists_finitePlace_of_prime_level (K₁ := K₂) (K₁' := K₂')
      (NK.Reconstruct.levelMap ϕ L) Q
    -- transport it back along the bijection of place systems
    obtain ⟨A, hA⟩ : ∃ A : NK.Reconstruct.FinitePlaceOf K₁ K₁', a.placeMap A = B :=
      ⟨a.placeMap.symm B, Equiv.apply_symm_apply a.placeMap B⟩
    -- the trace of `A` on the level `L` is the sought prime
    refine ⟨NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L), ?_⟩
    have hAspec : A.1.comap (algebraMap ↥L K₁') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
          (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)) :=
      NK.Reconstruct.primeOfLevel_spec A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
    -- the computation rule of `levelPrimeMapGen`, applied to the chosen place `A`
    rw [levelPrimeMapGen_spec ϕ hϕ a L _ A hAspec, hA]
    -- now compute the trace of `B` on the corresponding level
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (K := ↥(NK.Reconstruct.levelMap ϕ L))
    rw [← NK.Reconstruct.primeOfLevel_spec B.1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L))]
    exact hB

end NK.ReconstructField
