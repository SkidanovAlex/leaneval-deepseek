/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.GalRestrictCompat
import Submission.NK.Chebotarev.Basic

/-!
# Descent of Frobenius elements along a normal intermediate field

Let `K ⊆ E ⊆ M` be number fields with `M/K` finite Galois and `E/K` normal (hence Galois, since
`K` has characteristic zero).  For a prime `P` of `𝓞 M` and `σ ∈ Gal(M/K)`, the restriction
`σ|_E ∈ Gal(E/K)` is an arithmetic Frobenius at the prime `P ∩ 𝓞 E` of `𝓞 E` whenever `σ` is an
arithmetic Frobenius at `P`:

  `IsFrobAt P σ  →  IsFrobAt (P.under 𝓞E) (σ|_E)`.

The point is that the exponent occurring in the definition,
`Nat.card (𝓞 K ⧸ (P ∩ 𝓞 E) ∩ 𝓞 K) = Nat.card (𝓞 K ⧸ P ∩ 𝓞 K)`, is the *same* for `P` and for
`P ∩ 𝓞 E` (contraction of ideals is transitive), while the two defining congruences are
transported into each other by `NK.Chebotarev.galRestrict_restrictNormalHom`, the compatibility
of `galRestrict` with restriction to an intermediate field.  In particular no hypothesis on the
prime `p` of `K` below `P` is needed.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Chebotarev

open IsDedekindDomain

/-- **The prime of `𝓞 E` lying under `P` is the contraction of `P`.**  This is `rfl` for the
`asIdeal` of the `HeightOneSpectrum`-level `under`, and is recorded here so that the contraction
lemmas of `Ideal` apply. -/
lemma under_asIdeal {K M : Type*} [Field K] [Field M] [NumberField M] [Algebra K M]
    (E : IntermediateField K M) (P : PrimeIdeal M) :
    (P.under (NumberField.RingOfIntegers E)).asIdeal
      = Ideal.under (NumberField.RingOfIntegers E) P.asIdeal := rfl

/-- **Restriction of a Frobenius element to a normal intermediate field.**  Let `K ⊆ E ⊆ M` be a
tower of number fields with `M/K` finite Galois and `E/K` normal.  If `σ ∈ Gal(M/K)` is an
arithmetic Frobenius at the prime `P` of `𝓞 M`, then its restriction `σ|_E ∈ Gal(E/K)` is an
arithmetic Frobenius at the prime `P ∩ 𝓞 E` of `𝓞 E`. -/
theorem IsFrobAtRestrictNormalHom {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E : IntermediateField K M) [Normal K E]
    {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal M}
    (hP : P.asIdeal.LiesOver p.asIdeal) {σ : Gal(M/K)} (h : NK.Chebotarev.IsFrobAt P σ) :
    NK.Chebotarev.IsFrobAt (P.under (NumberField.RingOfIntegers E))
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E σ) := by
  intro y
  -- The contraction of primes is transitive, so the exponent of the congruence is the same
  -- for `P` and for `P ∩ 𝓞 E`.
  rw [under_asIdeal, Ideal.mem_under, map_sub, map_pow]
  -- `galRestrict` is compatible with the restriction `Gal(M/K) → Gal(E/K)`.
  erw [galRestrict_restrictNormalHom E σ y]
  rw [show Ideal.under (NumberField.RingOfIntegers K)
      (Ideal.under (NumberField.RingOfIntegers ↥E) P.asIdeal) =
      Ideal.under (NumberField.RingOfIntegers K) P.asIdeal from Ideal.under_under P.asIdeal]
  -- The congruence for `σ` at `P`, evaluated at `y` viewed in `𝓞 M`.
  exact h (algebraMap (NumberField.RingOfIntegers ↥E) (NumberField.RingOfIntegers M) y)

end NK.Chebotarev
