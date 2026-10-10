import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.FrobeniusBridge.LevelAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius bridge: the projective system of levels

The level-wise Frobenius condition `NK.FrobeniusBridge.frobAtLevel` is compatible with the
restriction maps of the projective system of finite normal levels: if `L ≤ M` and `g` is a
Frobenius element at the prime below the place `A` on `M`, then it is one on `L`.  The
mathematical content is the transitivity of the contraction of primes: the prime of `𝓞 L` below
`A` is the contraction of the prime of `𝓞 M` below `A`
(`NK.FrobeniusBridge.primeOfLevel_under`).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The prime below a place is the contraction of the prime below it on a larger level**: for
`L ≤ M` finite intermediate fields of `K'` and `A` a place of `K'` over a finite prime of `K`,
the prime of `𝓞 L` attached to `A` is the contraction to `𝓞 L` of the prime of `𝓞 M` attached to
`A`. -/
theorem primeOfLevel_under {L M : IntermediateField K K'} (hLM : L ≤ M)
    [FiniteDimensional K L] [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M] [IsScalarTower ↥L ↥M K']
    (A : FinitePlaceOf K K') :
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L) =
      (NK.Reconstruct.primeOfLevel A.1 M (NK.Reconstruct.comap_level_ne_top A.2 M)).under
        (NumberField.RingOfIntegers ↥L) := by
  have hM := NK.Reconstruct.primeOfLevel_spec A.1 M (NK.Reconstruct.comap_level_ne_top A.2 M)
  have hL := NK.Reconstruct.primeOfLevel_spec A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  haveI : FiniteDimensional ↥L ↥M := Module.Finite.of_restrictScalars_finite K ↥L ↥M
  have hcomap := Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
    (K := ↥L) (L := ↥M)
    ((NK.Reconstruct.primeOfLevel A.1 M
      (NK.Reconstruct.comap_level_ne_top A.2 M)).under (NumberField.RingOfIntegers ↥L))
    (NK.Reconstruct.primeOfLevel A.1 M (NK.Reconstruct.comap_level_ne_top A.2 M))
    (Ideal.over_under _)
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L)
  rw [← hL, ← hcomap, ← hM]
  ext x
  simp only [ValuationSubring.mem_comap]
  rw [← IsScalarTower.algebraMap_apply ↥L ↥M K' x]

/-- **Restriction of a Frobenius element to a level**: if `L ≤ M` and `g` is a Frobenius element
at the prime of `𝓞 M` below the place `A`, then it is one at the prime of `𝓞 L` below `A`. -/
theorem frobAtLevel_restrict {L M : IntermediateField K K'} (hLM : L ≤ M)
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M] [IsScalarTower ↥L ↥M K']
    (A : FinitePlaceOf K K') {g : Gal(K'/K)} (h : frobAtLevel A M g) : frobAtLevel A L g := by
  unfold frobAtLevel
  have h2 : NK.Chebotarev.IsFrobAt
      ((NK.Reconstruct.primeOfLevel A.1 M
        (NK.Reconstruct.comap_level_ne_top A.2 M)).under (NumberField.RingOfIntegers ↥L))
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L (AlgEquiv.restrictNormalHom M g)) :=
    NK.Chebotarev.isFrobAt_restrictNormalHom_le L M hLM h
  rw [← NK.Chebotarev.restrictNormalHom_le_comp L M hLM g] at h2
  rw [← primeOfLevel_under hLM A] at h2
  exact h2

end NK.FrobeniusBridge
