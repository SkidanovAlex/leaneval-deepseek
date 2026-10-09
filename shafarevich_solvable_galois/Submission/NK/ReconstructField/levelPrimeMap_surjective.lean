import Mathlib
import Submission.NK.ReconstructField.LevelPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the finite-level prime correspondence

The finite-level prime correspondence of CoNF XII §12.2,
`NK.ReconstructField.levelPrimeMap ϕ hϕ a L : PrimeIdeal ↥L → PrimeIdeal ↥(levelMap ϕ L)`,
is **surjective**: every prime `Q` of the corresponding level `levelMap ϕ L` arises as the image of
a prime of `L`.

The argument is the one recorded in `NK.ReconstructField.exists_place_comap_eq_of_liesOver`:
extend `Q` to a finite place `B` of `K₂'` (so that `B` restricts to the valuation ring `𝒪_{L₂,Q}`
on `levelMap ϕ L`); transport `B` back along the bijection `a.placeMap` of the two place systems to
a finite place `A` of `K₁'`; let `P` be the trace of `A` on the level `L`.  By the computation rule
`levelPrimeMap_spec`, `levelPrimeMap ϕ hϕ a L P` is computed from *any* place above `P`, in
particular from `A`, and equals the trace of `a.placeMap A = B` on `levelMap ϕ L`, i.e. `Q`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

theorem levelPrimeMap_surjective
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    Function.Surjective (NK.ReconstructField.levelPrimeMap ϕ hϕ a L) := by
  intro Q
  -- extend the prime `Q` of the corresponding level to a finite place of `K₂'`
  obtain ⟨B, hB⟩ := exists_finitePlace_of_prime_level (K₁ := K₂) (K₁' := K₂')
    (NK.Reconstruct.levelMap ϕ L) Q
  -- transport it back along the bijection of place systems
  obtain ⟨A, hA⟩ : ∃ A : NK.Reconstruct.FinitePlaceOf K₁ K₁', a.placeMap A = B :=
    ⟨a.placeMap.symm B, Equiv.apply_symm_apply a.placeMap B⟩
  -- the trace of `A` on the level `L` is the sought prime
  refine ⟨NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L), ?_⟩
  have hAeq : A.1.comap (algebraMap ↥L K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
        (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)) :=
    NK.Reconstruct.primeOfLevel_spec A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  -- the computation rule of `levelPrimeMap`, applied to the chosen place `A`
  have key : NK.ReconstructField.levelPrimeMap ϕ hϕ a L
        (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)) =
      NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) :=
    NK.ReconstructField.levelPrimeMap_spec ϕ hϕ a L _ A hAeq
  rw [key, hA]
  -- now compute the trace of `B` on the corresponding level
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (K := ↥(NK.Reconstruct.levelMap ϕ L))
  rw [← NK.Reconstruct.primeOfLevel_spec B.1 (NK.Reconstruct.levelMap ϕ L)
      (NK.Reconstruct.comap_level_ne_top B.2 (NK.Reconstruct.levelMap ϕ L))]
  exact hB

end NK.ReconstructField
