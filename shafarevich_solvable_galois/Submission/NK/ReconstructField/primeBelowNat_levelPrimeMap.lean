import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver
import Submission.NK.ReconstructField.levelPrimeMap_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-level prime correspondence preserves the rational prime below

The induced prime correspondence `NK.ReconstructField.levelPrimeMap ϕ hϕ a L` at a finite level
`L ⊆ K₁'` is compatible with the rational prime below a prime: for a prime `P` of `𝓞 L`, the prime
`levelPrimeMap ϕ hϕ a L P` of `𝓞 (levelMap ϕ L)` has the same rational prime below as `P`.  Since
`levelMap ϕ L` and `L` are extensions of the number fields `K₂` and `K₁`, whose rational primes are
matched by the local correspondence `a` (because `a` preserves the residue characteristic), the
assertion reduces to the two facts

* `NK.LocalInputs.primeBelow (↥L) P` is the rational prime below the prime of `K₁` under `P`
  (`primeBelow_under_eq`, transitivity of `Ideal.under` down to `ℤ`), and similarly for the level
  `levelMap ϕ L`;
* the prime of `𝓞 (levelMap ϕ L)` corresponding to `P` lies over the image of the prime of `K₁`
  under `P` (`NK.ReconstructField.levelPrimeMap_liesOver`), and the local correspondence matches
  rational primes (`primeBelow_primeMap`, from `a.residueChar`).
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

/-- **The rational prime below a prime of an extension is the rational prime below its trace.**
For a finite extension of number fields `L/K` and a prime `P` of `𝓞 L`, the rational prime below `P`
coincides with the rational prime below its trace `P ∩ 𝓞 K` on `K`.

Both sides are described by their underlying ideals: `(primeBelow L P).asIdeal` is the trace of
`P.asIdeal` to `𝓞 ℚ`, while the trace of the prime of `K` below `P` is `P.asIdeal.under (𝓞 K)`,
whose trace to `𝓞 ℚ` is again the trace of `P.asIdeal` (`Ideal.under_under`). -/
theorem primeBelow_under_eq {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (P : NK.Chebotarev.PrimeIdeal L) :
    NK.LocalInputs.primeBelow L P =
      NK.LocalInputs.primeBelow K
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) P) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.LocalInputs.primeBelow_asIdeal L P,
    NK.LocalInputs.primeBelow_asIdeal K
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) P),
    IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]

/-- **The local correspondence preserves the rational prime below a prime.**  For a prime `𝔭` of
`K₁`, the prime `a.primeMap 𝔭` of `K₂` has the same rational prime below: `a.residueChar` (in the
form `NK.ReconstructField.charP_primeMap`) preserves the residue characteristic of `𝔭`, and the
residue characteristic determines the rational prime below a prime
(`NK.ReconstructField.charP_of_liesOver` / `NK.ReconstructField.liesOver_of_charP`). -/
theorem primeBelow_primeMap {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁) :
    NK.LocalInputs.primeBelow K₂ (a.primeMap 𝔭) = NK.LocalInputs.primeBelow K₁ 𝔭 :=
  NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver (a.primeMap 𝔭)
    (NK.LocalInputs.primeBelow K₁ 𝔭)
    (NK.ReconstructField.liesOver_of_charP (a.primeMap 𝔭) (NK.LocalInputs.primeBelow K₁ 𝔭)
      (NK.ReconstructField.charP_primeMap a 𝔭 _
        (NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow K₁ 𝔭)
          (NK.LocalInputs.primeBelow_liesOver K₁ 𝔭))))

theorem primeBelowNat_levelPrimeMap {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    NK.LocalInputs.primeBelowNat ↥(NK.Reconstruct.levelMap ϕ L)
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) =
      NK.LocalInputs.primeBelowNat ↥L P := by
  -- the prime of `K₁` below `P`
  set 𝔭 : NK.Chebotarev.PrimeIdeal K₁ :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₁) P with h𝔭
  have hP : P.asIdeal.LiesOver 𝔭.asIdeal := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact Ideal.over_under P.asIdeal
  -- the trace of `levelPrimeMap ϕ hϕ a L P` on `K₂` is `a.primeMap 𝔭`
  have htr : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K₂)
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P) = a.primeMap 𝔭 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact (NK.ReconstructField.levelPrimeMap_liesOver ϕ hϕ a L 𝔭 P hP).over.symm
  -- reduce to the rational primes below `P` and `a.primeMap 𝔭` on the two base fields
  have h1 := primeBelow_under_eq (K := K₁) (L := ↥L) P
  have h2 := primeBelow_under_eq (K := K₂) (L := ↥(NK.Reconstruct.levelMap ϕ L))
    (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P)
  simp only [NK.LocalInputs.primeBelowNat]
  rw [h2, htr, primeBelow_primeMap a 𝔭, ← h1]

end NK.ReconstructField
