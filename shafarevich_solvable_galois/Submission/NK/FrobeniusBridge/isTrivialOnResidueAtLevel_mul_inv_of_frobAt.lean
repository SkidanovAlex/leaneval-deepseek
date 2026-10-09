import Mathlib
import Submission.NK.FrobeniusBridge.Bridge
import Submission.NK.FrobeniusBridge.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two Frobenius elements at a level differ by an element trivial on the residue field

This file proves `NK.FrobeniusBridge.isTrivialOnResidueAtLevel_mul_inv_of_frobAt`: if `σ` and `τ`
are both arithmetic Frobenius elements at the prime of the finite normal level `L` below the place
`A` (i.e. if `frobAtLevel A L σ` and `frobAtLevel A L τ` hold), then `σ * τ⁻¹` acts trivially on
the residue field of `L` at that prime.

This is the elementary half of the inertia description of the Frobenius coset: the two
congruences `σ x ≡ x ^ q` and `τ x ≡ x ^ q (mod P_L)` force `σ τ⁻¹ x ≡ x (mod P_L)`.

Formally it is the statement `IsArithFrobAt.mul_inv_mem_inertia` of Mathlib's Frobenius API
(`Mathlib.RingTheory.Frobenius`) applied to the action of `Gal(L/K)` on the ring of integers
`𝓞 L` through `galRestrict`, together with the fact that
`AlgEquiv.restrictNormalHom L` is a monoid homomorphism (so that
`(σ * τ⁻¹)|_L = σ|_L * (τ|_L)⁻¹`).
-/

set_option linter.style.haveILetI false

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

/-- **The ratio of two Frobenius elements at a level is trivial on the residue field.**

Let `A` be a place of `K'` over a finite prime of the number field `K`, and let `L ⊆ K'` be a
finite normal intermediate field with number field structure.  If `σ` and `τ` are both arithmetic
Frobenius elements at the prime `P_L` of `𝓞 L` below `A`, then `σ * τ⁻¹` acts trivially on the
residue field `𝓞 L ⧸ P_L` — that is, `σ * τ⁻¹` lies in the inertia subgroup of `P_L`.

This is the level-wise form of the classical fact that the Frobenius elements at a prime form a
coset of the inertia subgroup, and it is what makes the Frobenius "coset" of
`NK.FrobeniusBridge.PlaceLevelBridge` well defined at each finite level. -/
theorem isTrivialOnResidueAtLevel_mul_inv_of_frobAt {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] {σ τ : Gal(K'/K)}
    (hσ : NK.FrobeniusBridge.frobAtLevel A L σ) (hτ : NK.FrobeniusBridge.frobAtLevel A L τ) :
    NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L (σ * τ⁻¹) := by
  -- The Galois group of the level acts on its ring of integers through `galRestrict`.
  letI act : MulSemiringAction Gal(↥L/K) (NumberField.RingOfIntegers ↥L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K ↥L
      (NumberField.RingOfIntegers ↥L)
  haveI hcomm : SMulCommClass Gal(↥L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥L) :=
    ⟨fun g a x => by
      change galRestrict (NumberField.RingOfIntegers K) K ↥L
          (NumberField.RingOfIntegers ↥L) g
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers ↥L) a * x) =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers ↥L) a *
          galRestrict (NumberField.RingOfIntegers K) K ↥L
            (NumberField.RingOfIntegers ↥L) g x
      rw [map_mul, AlgEquiv.commutes]⟩
  -- Both restrictions are arithmetic Frobenius elements at the prime `P_L` below `A`.
  have hσ' : IsArithFrobAt (NumberField.RingOfIntegers K) (AlgEquiv.restrictNormalHom L σ)
      (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal :=
    hσ
  have hτ' : IsArithFrobAt (NumberField.RingOfIntegers K) (AlgEquiv.restrictNormalHom L τ)
      (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal :=
    hτ
  -- Hence their ratio lies in the inertia subgroup of `P_L`.
  have hmem := IsArithFrobAt.mul_inv_mem_inertia hσ' hτ'
  intro x
  have h := hmem x
  rw [map_mul, map_inv]
  exact h

end NK.FrobeniusBridge
