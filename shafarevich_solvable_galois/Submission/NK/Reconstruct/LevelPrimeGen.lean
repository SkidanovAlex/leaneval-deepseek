import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap
import Submission.NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level prime correspondence, for *arbitrary* finite levels

`NK.ReconstructField.levelPrimeMap` attaches to a prime `P` of a finite **normal** level
`L ⊆ K₁'` a prime of the corresponding level `levelMap ϕ L`, by choosing a finite place `A` of
`K₁'` above `P` and taking the prime of `levelMap ϕ L` below `a.placeMap A`.

The well-definedness of that prime (`NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq`)
uses only the transitivity of `Gal(K₁'/L)` on the places of `K₁'` over a fixed place of `L`
(`Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq`, which holds for an
*arbitrary* intermediate field `L`), the Galois equivariance of the place correspondence and the
fact that `levelMap ϕ L` is the fixed field of `ϕ(Gal(K₁'/L))`.  Normality of `L` is therefore not
needed, and this file records the general form, which is what the level-pair assembly of the
reconstruction needs (a finite level `L/K₁` is in general not normal).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']


/-- **The prime of the corresponding level attached to a prime of an arbitrary finite level.** -/
noncomputable def levelPrimeMapGen (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L) : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ L) :=
  NK.Reconstruct.primeOfLevel
    (a.placeMap (exists_finitePlace_of_prime_level L P).choose).1
    (NK.Reconstruct.levelMap ϕ L)
    (NK.Reconstruct.comap_level_ne_top
      (a.placeMap (exists_finitePlace_of_prime_level L P).choose).2
      (NK.Reconstruct.levelMap ϕ L))

/-- **The computation rule of `levelPrimeMapGen`**: the induced prime does not depend on the choice
of a place of `K₁'` above `P`. -/
theorem levelPrimeMapGen_spec (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L)
    (A : NK.Reconstruct.FinitePlaceOf K₁ K₁')
    (hA : A.1.comap (algebraMap ↥L K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P) :
    levelPrimeMapGen ϕ hϕ a L P =
      NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2
          (NK.Reconstruct.levelMap ϕ L)) := by
  unfold levelPrimeMapGen
  exact primeOfLevel_placeMap_eq_of_comap_eq_gen ϕ hϕ a L _ A (by
    rw [(exists_finitePlace_of_prime_level L P).choose_spec, hA])

end NK.ReconstructField

/-! ## Compatibility of the general level prime map with the base prime correspondence -/

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The general level prime map is compatible with the base prime correspondence**: if `P` lies
over `𝔭`, then `levelPrimeMapGen ϕ hϕ a L P` lies over `a.primeMap 𝔭`. -/
theorem levelPrimeMapGen_liesOver
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁) (P : NK.Chebotarev.PrimeIdeal ↥L)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    (levelPrimeMapGen ϕ hϕ a L P).asIdeal.LiesOver (a.primeMap 𝔭).asIdeal := by
  obtain ⟨A, hA⟩ :=
    NK.ReconstructField.exists_finitePlace_of_prime_level (K₁ := K₁) (K₁' := K₁') L P
  have hcomp : A.1.comap (algebraMap K₁ K₁') =
      (A.1.comap (algebraMap ↥L K₁')).comap (algebraMap K₁ ↥L) := by
    refine SetLike.ext fun x => ?_
    simp only [ValuationSubring.mem_comap]
    rw [IsScalarTower.algebraMap_apply K₁ ↥L K₁']
  have hcomap : A.1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭 := by
    rw [hcomp, hA, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime 𝔭 P hP]
  have hprime : Submission.NeukirchUchida.primeOf A.1 A.2 = 𝔭 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁) (by
      rw [← Submission.NeukirchUchida.primeOf_spec A.1 A.2, hcomap])
  rw [levelPrimeMapGen_spec ϕ hϕ a L P A hA, ← hprime, a.primeMap_spec A]
  have hkey : NK.Reconstruct.primeOfLevel (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
      (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)) =
      Submission.NeukirchUchida.Local.placeOf
        (Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2)
        (a.placeMap A).1
        (Submission.NeukirchUchida.primeOf_spec (a.placeMap A).1 (a.placeMap A).2)
        (NK.Reconstruct.levelMap ϕ L) := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (K := ↥(NK.Reconstruct.levelMap ϕ L)) ?_
    rw [← NK.Reconstruct.primeOfLevel_spec]
    rw [← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf]
  rw [hkey]
  exact Submission.NeukirchUchida.Local.placeOf_liesOver _ _ _ _

end NK.ReconstructField

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The general level prime correspondence preserves the rational prime below**, for an
arbitrary finite level. -/
theorem primeBelowNat_levelPrimeMapGen
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    NK.LocalInputs.primeBelowNat ↥(NK.Reconstruct.levelMap ϕ L)
        (levelPrimeMapGen ϕ hϕ a L P) =
      NK.LocalInputs.primeBelowNat ↥L P := by
  set 𝔭 : NK.Chebotarev.PrimeIdeal K₁ :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₁) P with h𝔭
  have hP : P.asIdeal.LiesOver 𝔭.asIdeal := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact Ideal.over_under P.asIdeal
  have htr : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₂)
        (levelPrimeMapGen ϕ hϕ a L P) = a.primeMap 𝔭 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact (levelPrimeMapGen_liesOver ϕ hϕ a L 𝔭 P hP).over.symm
  have h1 := primeBelow_under_eq (K := K₁) (L := ↥L) P
  have h2 := primeBelow_under_eq (K := K₂) (L := ↥(NK.Reconstruct.levelMap ϕ L))
    (levelPrimeMapGen ϕ hϕ a L P)
  simp only [NK.LocalInputs.primeBelowNat]
  rw [h2, htr, primeBelow_primeMap a 𝔭, ← h1]

end NK.ReconstructField
