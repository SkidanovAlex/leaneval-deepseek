import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.NK.Chebotarev.Density
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Chebotarev.IsFrobAtConj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius elements at two primes over `p` are conjugate

For a finite Galois extension `L/K` of number fields, `p` a prime of `𝓞 K` unramified in `L`, and
`P, Q` two primes of `𝓞 L` above `p`, the Frobenius elements `Frob(P)` and `Frob(Q)` are conjugate
in `Gal(L/K)`.  Since the Frobenius at a prime is unique (`IsFrobAt.eq_of_isFrobAt`) once the prime
is unramified, it suffices to find `g` with `g • P = Q` — which exists because the Galois group acts
transitively on the primes above `p` — and to use the equivariance of the Frobenius
(`IsFrobAtConj`): `g * Frob(P) * g⁻¹` is a Frobenius at `g • P = Q`.

This is the statement that makes `Frob_p` well defined up to conjugacy, hence the input to the
Čebotarev density theorem in the form "the density of the primes with Frobenius in a conjugacy
class".
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Chebotarev

/-- **The Frobenius elements at two primes above the same unramified prime are conjugate.**
Let `L/K` be a finite Galois extension of number fields, `p` a prime of `𝓞 K` unramified in `L`,
and `P, Q` two primes of `𝓞 L` above `p`.  Then the Frobenius at `P` and the Frobenius at `Q` are
conjugate in `Gal(L/K)`. -/
theorem ConjugacyOfFrobenius {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : NK.Chebotarev.PrimeIdeal K) (P Q : NK.Chebotarev.PrimeIdeal L)
    (hP : P.asIdeal.LiesOver p.asIdeal) (hQ : Q.asIdeal.LiesOver p.asIdeal)
    (hunr : ∀ R : NK.Chebotarev.PrimeIdeal L, R.asIdeal.LiesOver p.asIdeal →
      R.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ τ : Gal(L/K)) (hσ : NK.Chebotarev.IsFrobAt P σ) (hτ : NK.Chebotarev.IsFrobAt Q τ) :
    ∃ g : Gal(L/K), τ = g * σ * g⁻¹ := by
  -- Transitivity of the Galois action on the primes above `p`, in the form of ideals: there is
  -- `g` with `g • Q = P`, i.e. `Q.comap (galRestrict g) = P`.
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (NumberField.RingOfIntegers K) K L
    (NumberField.RingOfIntegers L) (p := p.asIdeal) (P₁ := Q.asIdeal) (P₂ := P.asIdeal)
    ⟨Q.2, hQ⟩ ⟨P.2, hP⟩
  -- Since `galRestrict g` is bijective, taking images turns the contraction back into `Q`.
  have hmap : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) g :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) P.asIdeal = Q.asIdeal := by
    rw [← hg]
    exact Ideal.map_comap_of_surjective _ (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) g).surjective Q.asIdeal
  -- This is exactly the statement that `g • P = Q` for the action on `PrimeIdeal L`.
  have hsmul : g • P = Q := IsDedekindDomain.HeightOneSpectrum.ext hmap
  -- Hence `g * σ * g⁻¹` is a Frobenius at `Q` by equivariance of the Frobenius.
  have hgσ : NK.Chebotarev.IsFrobAt Q (g * σ * g⁻¹) := by
    rw [← hsmul]
    exact NK.Chebotarev.IsFrobAtConj hσ
  -- Uniqueness of the Frobenius at the unramified prime `Q` concludes.
  exact ⟨g, ((NK.Chebotarev.IsFrobAt.eq_of_isFrobAt (p := p) hQ (hunr Q hQ) hgσ hτ).symm)⟩

end NK.Chebotarev
