/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The primes of a subfield above a rational prime, at an arbitrary universe

Universe-polymorphic copy of `NK.WeakNU.primeCountAbove_under_eq_primesOverRat`.

For `N/ℚ` a finite Galois extension of number fields (`N : Type u`), `M ⊆ N` an intermediate
field, and `P` a prime of `𝓞 N` above the rational prime `p`, the number of primes of `𝓞 M` above
the place of `ℚ` below `P` equals the number of primes of `𝓞 M` above `p`:

`NK.UniverseWeakNU.primeCountAboveU_under_eq_primesOverRatU`.

The mathematical content is that `ℚ` has a **unique** prime above `p`: the base ring map
`ℤ → 𝓞 ℚ` is bijective, so contracting ideals along it loses no information
(`NK.UniverseWeakNU.liesOver_iff_liesOver_comap_of_surjectiveU`), and the contraction of the
place of `𝓞 ℚ` below `P` back to `ℤ` is `p ℤ` by the transitivity of `Ideal.under`.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.PrimeOrbitU
import Submission.NK.UniverseWeakNU.Defs

open IsDedekindDomain

namespace NK.UniverseWeakNU

universe u

/-- **Lying over is insensitive to a bijective change of the base.**

Consider a tower of rings `A → B → C` in which the first map `algebraMap A B` is surjective (so a
bijection, as it is injective whenever `A` is a domain of characteristic zero and `B` has no
`ℤ`-torsion — in particular for `A = ℤ`, `B = 𝓞 ℚ`).  Then for an ideal `J` of `C` and an ideal `I`
of `B`, `J` lies over `I` (over the base `B`, i.e. `J.under B = I`) if and only if `J` lies over
`I.comap (algebraMap A B)` (over the base `A`).

Indeed `J.under A = (J.under B).under A` (`Ideal.under_under`), and contraction along a surjective
ring hom is injective. -/
theorem liesOver_iff_liesOver_comap_of_surjectiveU {A B C : Type*} [CommSemiring A]
    [CommSemiring B] [Semiring C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (hAB : Function.Surjective (algebraMap A B)) (J : Ideal C)
    (I : Ideal B) : J.LiesOver I ↔ J.LiesOver (I.comap (algebraMap A B)) := by
  rw [Ideal.liesOver_iff, Ideal.liesOver_iff]
  have h : J.under A = (J.under B).comap (algebraMap A B) := by
    rw [← Ideal.under_under (A := A) (B := B) J, Ideal.under_def (A := A) (P := J.under B)]
  rw [h]
  exact ((Ideal.comap_injective_of_surjective (algebraMap A B) hAB).eq_iff).symm

/-- **The contraction of a prime of `𝓞 N` to `𝓞 ℚ` contracts further to the rational prime `p`.**

If `P` lies over `p ℤ ⊆ ℤ`, then the place `𝔭` of `ℚ` below `P` contracts to `p ℤ` under the
bijection `ℤ ≃ 𝓞 ℚ`: `𝔭.asIdeal.comap (algebraMap ℤ (𝓞 ℚ)) = p ℤ`. -/
theorem under_asIdeal_comap_eq_spanU {N : Type u} [Field N] [NumberField N] [Algebra ℚ N]
    (p : ℕ) (P : NK.Chebotarev.PrimeIdeal N)
    (hP : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P).asIdeal.comap
        (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) = Ideal.span {(p : ℤ)} := by
  rw [HeightOneSpectrum.under_asIdeal]
  rw [← Ideal.under_def]
  rw [Ideal.under_under]
  exact hP.over.symm

/-- **The count of the primes of a subfield above a rational prime**, at an arbitrary universe.

For a finite Galois extension `N/ℚ` (`N : Type u`), an intermediate field `M ⊆ N`, a rational prime
`p` and a prime `P` of `𝓞 N` above `p`, the number of primes of `𝓞 M` above the place of `ℚ` below
`P` is the number of primes of `𝓞 M` above `p`.

Equivalently: since `ℚ` has exactly one prime above `p`, the indexing place `𝔭` of `ℚ` below `P` is
the same as `p ℤ` for every purpose, so the two counts coincide. -/
theorem primeCountAboveU_under_eq_primesOverRatU {N : Type u} [Field N] [NumberField N]
    [Algebra ℚ N] [IsGalois ℚ N] (M : IntermediateField ℚ N) (p : ℕ)
    (P : NK.Chebotarev.PrimeIdeal N) (hP : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)})) :
    primeCountAbove M (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P) =
      Nat.card (NK.UchidaKummer.primesOverRat ↥M p) := by
  have h𝔭 := under_asIdeal_comap_eq_spanU p P hP
  unfold primeCountAbove NK.UchidaKummer.primesOverRat
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun 𝔮 => ?_))
  simp only [Set.mem_ofPred_eq]
  rw [liesOver_iff_liesOver_comap_of_surjectiveU (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
    (C := NumberField.RingOfIntegers ↥M)
    (Rat.int_algebraMap_surjective (NumberField.RingOfIntegers ℚ))
    𝔮.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P).asIdeal, h𝔭]

end NK.UniverseWeakNU
