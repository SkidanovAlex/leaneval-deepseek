/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of Frobenius elements to subfields

Let `K' / K` be a Galois extension of the number field `K` (possibly of infinite degree) and let
`L ≤ M` be finite normal intermediate fields.  This file proves that the restriction of a
Frobenius element at a prime `P` of `𝓞 M` to the subfield `L` is a Frobenius element at the
prime `P ∩ 𝓞 L` of `𝓞 L`:

`IsFrobAt P ρ → IsFrobAt (P ∩ 𝓞 L) (ρ|_L)`,

together with the compatibility of the restriction maps `Gal(M/K) →* Gal(L/K)` with the
restriction maps to `Gal(K'/K)`.  These are the descent statements that make the Frobenius
elements of the finite levels of `K'/K` a projective system, and are used to run the compactness
argument producing an element of `Gal(K'/K)` whose restriction to every finite normal
intermediate field is a Frobenius element at a prime above a fixed prime `p` of `K`.

The proofs are the same as those of `NK.Chebotarev.galRestrict_restrictNormalHom`, but with the
subfield `L` an intermediate field of `K'` rather than of `M`, so that the *algebra* structure
`Algebra ↥L ↥M` is not an instance and is supplied by the caller.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

open IsDedekindDomain

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- **Compatibility of `galRestrict` with restriction to a subfield.**  Let `L ≤ M` be finite
normal intermediate fields of the Galois extension `K'/K`.  For `ρ ∈ Gal(M/K)` and `y ∈ 𝓞 L`,
the element of `𝓞 M` obtained by applying (the automorphism of `𝓞 M` induced by) the restriction
`ρ|_L ∈ Gal(L/K)` to `y` is the same as the one obtained by applying `ρ` to `y`. -/
theorem algebraMap_galRestrict_restrictNormalHom_le (L M : IntermediateField K K') (hLM : L ≤ M)
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M]
    (ρ : Gal(↥M/K)) (y : NumberField.RingOfIntegers ↥L) :
    algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M)
      ((AlgEquiv.toAlgHom (galRestrict (NumberField.RingOfIntegers K) K ↥L
        (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L ρ))) y)
      = galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M) ρ
          (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M) y) := by
  have h : algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M)
      ((galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L ρ)) y)
      = galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M) ρ
          (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M) y) := by
    have hM : algebraMap (NumberField.RingOfIntegers ↥M) ↥M
        (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M)
          ((galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
            (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L ρ)) y))
        = algebraMap (NumberField.RingOfIntegers ↥M) ↥M
          (galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M) ρ
            (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M) y)) := by
      conv_lhs => rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L)
        (NumberField.RingOfIntegers ↥M) ↥M]
      conv_rhs => rw [algebraMap_galRestrict_apply]
      conv_lhs => rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L ↥M]
      conv_lhs => rw [algebraMap_galRestrict_apply]
      conv_lhs => rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L ρ) =
          ρ.restrictNormal ↥L from rfl]
      conv_lhs => rw [AlgEquiv.restrictNormal_commutes]
      conv_rhs => rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L)
        (NumberField.RingOfIntegers ↥M) ↥M]
      conv_rhs => rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L ↥M]
    exact IsFractionRing.injective (NumberField.RingOfIntegers ↥M) ↥M hM
  exact h

/-- **Descent of a Frobenius element to a subfield.**  Let `L ≤ M` be finite normal intermediate
fields of the Galois extension `K'/K`.  If `ρ ∈ Gal(M/K)` is a Frobenius element at the prime `P`
of `𝓞 M`, then its restriction `ρ|_L` is a Frobenius element at the prime `P ∩ 𝓞 L` of `𝓞 L`. -/
theorem isFrobAt_restrictNormalHom_le (L M : IntermediateField K K') (hLM : L ≤ M)
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M]
    {P : PrimeIdeal ↥M} {ρ : Gal(↥M/K)} (hρ : IsFrobAt P ρ) :
    IsFrobAt (P.under (NumberField.RingOfIntegers ↥L))
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L ρ) := by
  intro y
  have hN : Nat.card (NumberField.RingOfIntegers K ⧸
      (P.under (NumberField.RingOfIntegers ↥L)).asIdeal.under (NumberField.RingOfIntegers K)) =
      Nat.card (NumberField.RingOfIntegers K ⧸
        P.asIdeal.under (NumberField.RingOfIntegers K)) := by
    rw [show (P.under (NumberField.RingOfIntegers ↥L)).asIdeal =
      P.asIdeal.under (NumberField.RingOfIntegers ↥L) from rfl, Ideal.under_under]
  rw [hN, show (P.under (NumberField.RingOfIntegers ↥L)).asIdeal =
    P.asIdeal.under (NumberField.RingOfIntegers ↥L) from rfl,
    Ideal.mem_under (NumberField.RingOfIntegers ↥L) P.asIdeal, map_sub, map_pow]
  rw [algebraMap_galRestrict_restrictNormalHom_le L M hLM ρ y]
  exact hρ (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers ↥M) y)

/-- **The restriction maps are compatible along a tower of intermediate fields.**  For `L ≤ M`
intermediate fields of `K'` and `σ : Gal(K'/K)`, restricting `σ` to `L` is the same as
restricting `σ` to `M` and then to `L`. -/
theorem restrictNormalHom_le_comp (L M : IntermediateField K K') (hLM : L ≤ M)
    [Normal K L] [Normal K M]
    [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M] [IsScalarTower ↥L ↥M K']
    (σ : Gal(K'/K)) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) ↥L
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M σ) := by
  exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥L) (K₂ := ↥M)
    (F := K) (K₃ := K') σ

/-- **Descent of `IsFrobAtPrime` along an inclusion of finite normal intermediate fields.**
If `σ ∈ Gal(K'/K)` restricts on `M` to a Frobenius element at some prime of `𝓞 M` above `p`, then
it restricts on every subfield `L ≤ M` to a Frobenius element at some prime of `𝓞 L` above `p`. -/
theorem exists_isFrobAtPrime_of_le (L M : IntermediateField K K') (hLM : L ≤ M)
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    {p : PrimeIdeal K} {σ : Gal(K'/K)}
    (h : ∃ P : PrimeIdeal ↥M, P.asIdeal.LiesOver p.asIdeal ∧
      IsFrobAt P (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M σ)) :
    ∃ P' : PrimeIdeal ↥L, P'.asIdeal.LiesOver p.asIdeal ∧
      IsFrobAt P' (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) := by
  letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI : IsScalarTower K ↥L ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ↥L ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
  obtain ⟨P, hP, hPfrob⟩ := h
  refine ⟨P.under (NumberField.RingOfIntegers ↥L), ?_, ?_⟩
  · refine ⟨?_⟩
    rw [show (P.under (NumberField.RingOfIntegers ↥L)).asIdeal =
      P.asIdeal.under (NumberField.RingOfIntegers ↥L) from rfl, Ideal.under_under]
    exact hP.over
  · rw [restrictNormalHom_le_comp L M hLM σ]
    exact isFrobAt_restrictNormalHom_le L M hLM hPfrob

end NK.Chebotarev
