/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.Basic

/-!
# Frobenius elements at conjugate primes

The Frobenius element at a prime is not invariant under the action of the Galois group on the
primes: conjugating the automorphism transports the prime.  Precisely, for a finite Galois
extension `L/K` of number fields, a prime `P` of `𝓞 L` and `σ, τ ∈ Gal(L/K)`,

  `IsFrobAt P σ  →  IsFrobAt (τ • P) (τ * σ * τ⁻¹)`.

This is the conjugacy-invariance of the Frobenius, the statement that makes
`IsFrobAtPrime` well defined up to conjugacy and that underlies the Čebotarev density theorem.

The proof is the general ring-theoretic statement `IsArithFrobAt.conj` (Mathlib), transported
along the identification `galRestrict A K L B : Gal(L/K) ≃* (B ≃ₐ[A] B)` of the Galois group
with the `A`-algebra automorphisms of the ring of integers: the canonical `Gal(L/K)`-action on
`𝓞 L` (`IsIntegralClosure.MulSemiringAction`) is exactly the action through `galRestrict`, so
the prime `τ • P` of `𝓞 L` corresponds to the pointwise transport `τ • P.asIdeal` of ideals,
and `IsFrobAt P σ` is verbatim the predicate `IsArithFrobAt (𝓞 K) σ P.asIdeal`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open scoped Pointwise

/-- **The Frobenius element is equivariant for the action of the Galois group on primes.**
If `σ` is an arithmetic Frobenius at the prime `P` of `𝓞 L`, then `τ * σ * τ⁻¹` is an
arithmetic Frobenius at the conjugate prime `τ • P`. -/
theorem IsFrobAtConj {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {P : NK.Chebotarev.PrimeIdeal L} {σ τ : Gal(L/K)} (h : NK.Chebotarev.IsFrobAt P σ) :
    NK.Chebotarev.IsFrobAt (τ • P) (τ * σ * τ⁻¹) := by
  -- The canonical action of `Gal(L/K)` on the ring of integers `𝓞 L`, through `galRestrict`.
  letI act : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hcomm : SMulCommClass Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    ⟨fun g a x => by
      change galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) g
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a * x) =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a *
          galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) g x
      rw [map_mul, AlgEquiv.commutes]⟩
  -- `IsFrobAt P σ` is `IsArithFrobAt (𝓞 K) σ P.asIdeal` by definition of the action.
  have h' : IsArithFrobAt (NumberField.RingOfIntegers K) σ P.asIdeal := h
  -- Transport along the action: the Frobenius conjugates to the conjugate prime.
  have h'' : IsArithFrobAt (NumberField.RingOfIntegers K) (τ * σ * τ⁻¹) (τ • P).asIdeal :=
    h'.conj τ
  exact h''

end NK.Chebotarev
