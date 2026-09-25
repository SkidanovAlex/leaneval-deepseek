import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Norm

namespace NK.CFTLib.Existence

open NumberField

/-- **Ramification index in a prime degree Galois extension.**

Let `L / K` be a finite Galois extension of number fields of prime degree `p`, let `Q` be a
nonzero prime of `𝓞 K` and `q` a prime of `𝓞 L` lying over `Q`. Then the ramification index
`e(q | Q)` is either `1` or `p`.

Mathematically this is the fundamental identity `[L : K] = ∑_{q | Q} e(q|Q) f(q|Q)` combined
with the fact that `L / K` is Galois: the Galois group acts transitively on the primes over `Q`,
so all ramification indices (and all inertia degrees) coincide and `g · e · f = [L : K] = p`.
In Mathlib this is packaged by `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`,
which states `ncard (primesOver Q (𝓞 L)) * (e * f) = Nat.card Gal(L/K)`, together with
`IsGalois.card_aut_eq_finrank`. -/
theorem ramificationIdx_eq_one_or_eq_prime_of_finrank_eq_prime
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∨
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = p := by
  classical
  -- The Galois group of `L/K` has cardinality `p = [L : K]`.
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  -- The Galois fundamental identity: `g · (e · f) = |Gal(L/K)|`.
  have key := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Q.asIdeal) (NumberField.RingOfIntegers L) (L ≃ₐ[K] L)
  -- Hence `e` divides `|Gal(L/K)| = p`.
  have hdvd : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) ∣ p := by
    rw [← hcard, ← key]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  -- `ramificationIdxIn` agrees with the ramification index of any prime over `Q`.
  have heq : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal q.asIdeal (L ≃ₐ[K] L)
  rw [heq] at hdvd
  exact (Nat.dvd_prime hp).mp hdvd

end NK.CFTLib.Existence
