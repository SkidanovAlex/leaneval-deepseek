import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
import Submission.NK.Chebotarev.exists_restrictNormalHom_eq_and_isFrobAtPrime
import Submission.NK.NUV2.ARL.abelianWeakToStrong

/-!
# The Artin symbol is compatible with restriction to an intermediate field

For a finite abelian extension `L / K` of number fields and an intermediate field `M`
(finite, normal, hence Galois over `K`), the restriction of the ideal-theoretic Artin symbol
`NK.CFTLib.ArtinReciprocityIdeal.artinSymbol K L 𝔞` to `Gal(↥M/K)` is the Artin symbol
`artinSymbol K ↥M 𝔞` of the subextension — *as long as every prime dividing `𝔞` is unramified in
`L`*.

That hypothesis is essential and not a technicality: `frobSymbol` is defined to be `1` at a
*ramified* prime, and a prime of `K` may well be ramified in `L` but unramified in `M` (the
ramification can happen in the layer `L/M`).  In that case the restriction of the symbol of `L`
would be `1` while the symbol of `M` is a non-trivial Frobenius, and the identity fails.  For
*unramified* primes, though, the Frobenius is well defined and the restriction of a Frobenius
element at `p` in `L/K` is a Frobenius element at `p` in `M/K`
(`NK.CFTLib.exists_isFrobAtPrime_restrict`), so the two symbols agree prime by prime.

The proof is therefore: unfold both `artinSymbol`s into the product over the multiset
`normalizedFactors 𝔞`, and compare term by term — each prime in `normalizedFactors 𝔞` is a
non-zero prime ideal (`UniqueFactorizationMonoid.prime_of_normalized_factor`,
`UniqueFactorizationMonoid.ne_zero_of_normalizedFactors`) dividing `𝔞`, hence unramified in `L`
by hypothesis and in `M` by descent
(`NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField`).

The two auxiliary lemmas convert between the two costumes worn by unramifiedness in this
workspace: the `𝔭`-indexed `IsUnramified` (used by `frobSymbol`) and the ideal-theoretic
`Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1`.

This is the input `(R1)` of `NOTES_analysis.md`: it lets one build the Artin map of an abelian
extension out of the Artin maps of its cyclic subextensions.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NK.Chebotarev NumberField
open scoped NumberField IsMulCommutative

namespace NK.NUV2.RouteB.LangX

section Unramified

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Unramifiedness in the `IsUnramified` costume.**  If the ramification index of `p` in the
extension `𝓞 K ⊆ 𝓞 L` is `1` then every prime of `𝓞 L` above `p` has ramification index `1` over
`p`.  (The two formulations are equivalent because the Galois group permutes the primes above
`p`.) -/
lemma isUnramified_of_ramificationIdxIn_eq_one [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeIdeal K) (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p := by
  intro P hP
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal P.asIdeal
    (Gal(L/K))]
  exact h

/-- **Descent of unramifiedness to an intermediate field**, in the `IsUnramified` costume: a
prime unramified in `L/K` is unramified in `M/K` for `K ⊆ M ⊆ L`. -/
lemma isUnramified_intermediateField [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [IsGalois K ↥M]
    (p : PrimeIdeal K) (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p :=
  isUnramified_of_ramificationIdxIn_eq_one p
    (NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (M := M) p h)

end Unramified

section Restrict

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

/-- **The chosen Frobenius element restricts to the chosen Frobenius element.**  For an
intermediate field `K ⊆ M ⊆ L` and a prime `p` of `K` unramified in `L` (hence in `M`), the
restriction of `frobAtPrime p ∈ Gal(L/K)` to `Gal(↥M/K)` is `frobAtPrime p ∈ Gal(↥M/K)`.

Both sides are characterised by `IsFrobAtPrime` at the unramified prime `p`
(`isFrobAtPrime_iff_frobAtPrime_eq`), and the restriction of a Frobenius element at `p` in `L/K`
is a Frobenius element at `p` in `M/K` (`NK.CFTLib.exists_isFrobAtPrime_restrict`). -/
lemma frobAtPrime_restrictNormalHom
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (↥M ≃ₐ[K] ↥M)]
    (p : PrimeIdeal K) (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M (frobAtPrime (K := K) (L := L) p)
      = frobAtPrime (K := K) (L := ↥M) p := by
  classical
  have hcommL : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  have hcommM : ∀ a b : Gal(↥M/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  have hL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p :=
    isUnramified_of_ramificationIdxIn_eq_one p h
  have hM : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p :=
    isUnramified_intermediateField M p h
  obtain ⟨σ, hσ⟩ := exists_isFrobAtPrime (K := K) (L := L) p
  have h1 : frobAtPrime (K := K) (L := L) p = σ :=
    (isFrobAtPrime_iff_frobAtPrime_eq hcommL p hL σ).mp hσ
  have h2 : frobAtPrime (K := K) (L := ↥M) p
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M σ :=
    (isFrobAtPrime_iff_frobAtPrime_eq hcommM p hM _).mp
      (NK.CFTLib.exists_isFrobAtPrime_restrict M hσ)
  rw [h1, h2]

end Restrict

/-- **The ideal-theoretic Artin symbol is compatible with restriction to an intermediate field**,
provided every prime dividing the ideal is unramified in the big extension. -/
theorem artinSymbol_restrictNormalHom {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (↥M ≃ₐ[K] ↥M)]
    (𝔞 : Ideal (NumberField.RingOfIntegers K))
    (hunr : ∀ p : NK.Chebotarev.PrimeIdeal K, p.asIdeal ∣ 𝔞 →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.ArtinReciprocityIdeal.artinSymbol (K := K) (L := L) 𝔞)
      = NK.CFTLib.ArtinReciprocityIdeal.artinSymbol (K := K) (L := ↥M) 𝔞 := by
  classical
  -- term-by-term comparison of the two products over `normalizedFactors 𝔞`
  have key : ∀ x ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
          (NK.CFTLib.ArtinReciprocityIdeal.frobSymbol (K := K) (L := L) x)
        = NK.CFTLib.ArtinReciprocityIdeal.frobSymbol (K := K) (L := ↥M) x := by
    intro x hx
    -- `x` is a non-zero prime ideal dividing `𝔞`
    have hne : x ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hx
    have hnebot : x ≠ ⊥ := hne
    have hprime : x.IsPrime :=
      (Ideal.prime_iff_isPrime hnebot).mp
        (UniqueFactorizationMonoid.prime_of_normalized_factor x hx)
    let q : PrimeIdeal K := ⟨x, hprime, hnebot⟩
    have hdvd : q.asIdeal ∣ 𝔞 := by
      simpa [q] using UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx
    have hq : Ideal.ramificationIdxIn q.asIdeal (𝓞 L) = 1 := hunr q hdvd
    have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) q :=
      isUnramified_of_ramificationIdxIn_eq_one q hq
    have hunrM : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) q :=
      isUnramified_intermediateField M q hq
    rw [NK.CFTLib.ArtinReciprocityIdeal.frobSymbol_eq (K := K) (L := L) q hunrL,
      NK.CFTLib.ArtinReciprocityIdeal.frobSymbol_eq (K := K) (L := ↥M) q hunrM]
    exact frobAtPrime_restrictNormalHom M q hq
  unfold NK.CFTLib.ArtinReciprocityIdeal.artinSymbol
  rw [MonoidHom.map_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl (fun x hx => key x hx))

end NK.NUV2.RouteB.LangX
