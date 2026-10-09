import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocity law at a modulus supported on the ramified primes

The ideal-theoretic reciprocity law of `NK.CFTLib.ArtinReciprocityIdeal` (Lang, *ANT* X §1–2)
supplies, for every finite abelian extension `L / K` of number fields, a modulus `m` such that the
product of the Frobenius elements of the prime factors of any `(a)` with `a ≡ 1 mod (m)` totally
positive is trivial, and such that every prime not dividing `(m)` is unramified.

The classical form of the law is stronger: the modulus can always be chosen with **support
contained in the ramified primes** (equivalently: the Artin symbol `𝔭 ↦ Frob_𝔭` is well defined
modulo the conductor; Neukirch, *Algebraic Number Theory*, V.6.1 / Lang X §4).  This is the form in
which the law gives the Frobenius normalisation of the Artin map at *every* unramified prime,
including those dividing the modulus supplied by the raw form.

The statement below is that stronger form, as a `Prop`.
-/

open NumberField

namespace NK.NUV2

/-- **The reciprocity law with a modulus supported on the ramified primes.**

For every finite abelian extension `L / K` of number fields there is `m > 0` such that every prime
dividing `(m)` is ramified in `L / K`, and such that the product of the Frobenius elements at the
prime factors of any `(a)`, with multiplicity, is trivial whenever `a ≡ 1 mod (m)` and `a` is
totally positive (the primes occurring being automatically coprime to `(m)`). -/
def ArtinReciprocityIdealRamified : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) →
    ∃ m : Ideal (𝓞 K), m ≠ ⊥ ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        p.asIdeal ∣ m → Ideal.ramificationIdxIn p.asIdeal (𝓞 L) ≠ 1) ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        Ideal.ramificationIdxIn p.asIdeal (𝓞 L) ≠ 1 → p.asIdeal ∣ m) ∧
      ∀ (a : 𝓞 K), a - 1 ∈ m → (∀ φ : K →+* ℝ, 0 < φ (a : K)) →
      ∀ (s : Finset (NK.Chebotarev.PrimeIdeal K)) (e : NK.Chebotarev.PrimeIdeal K → ℕ)
        (σ : NK.Chebotarev.PrimeIdeal K → (L ≃ₐ[K] L)),
        (∀ p ∈ s, ¬ p.asIdeal ∣ m) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1

end NK.NUV2
