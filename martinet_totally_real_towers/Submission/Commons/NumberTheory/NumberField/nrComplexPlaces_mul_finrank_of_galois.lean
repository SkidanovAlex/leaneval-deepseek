import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

/-- **Complex places multiply along Galois infinite-unramified extensions.**

For a Galois extension `k ⊆ K` of number fields unramified at all infinite places, the number of
complex places multiplies by the degree: `r₂(K) = [K : k] · r₂(k)`.

Proof: `NumberField.InfinitePlace.IsUnramifiedAtInfinitePlaces.card_infinitePlace` (Mathlib,
`NumberTheory/NumberField/InfinitePlace/Ramification.lean`) gives
`#InfinitePlace K = #InfinitePlace k * finrank k K`; combined with
`NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces` and
`NumberField.InfinitePlace.card_add_two_mul_card_eq_rank` (for `k` and for `K`, together with
`Module.finrank_mul_finrank`) this yields the identity after cancelling `2`. -/
theorem nrComplexPlaces_mul_finrank_of_galois (k K : Type*) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] :
    NumberField.InfinitePlace.nrComplexPlaces K =
      Module.finrank k K * NumberField.InfinitePlace.nrComplexPlaces k := by
  set A := NumberField.InfinitePlace.nrRealPlaces K with hA
  set B := NumberField.InfinitePlace.nrComplexPlaces K with hB
  set a := NumberField.InfinitePlace.nrRealPlaces k with ha
  set b := NumberField.InfinitePlace.nrComplexPlaces k with hb
  set n := Module.finrank k K with hn
  -- `A + 2B = [K : ℚ]` and `a + 2b = [k : ℚ]`
  have hK := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [← hA, ← hB] at hK
  have hk := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank k
  rw [← ha, ← hb] at hk
  -- `A + B = #InfinitePlace K`, `a + b = #InfinitePlace k`
  have hcK := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [← hA, ← hB] at hcK
  have hck := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces k
  rw [← ha, ← hb] at hck
  -- tower law
  have hfr : Module.finrank ℚ K = Module.finrank ℚ k * n := by
    rw [hn]
    exact (Module.finrank_mul_finrank (F := ℚ) (K := k) (A := K)).symm
  -- `A + B = (a + b) * n`
  have hcard : A + B = (a + b) * n := by
    have h := IsUnramifiedAtInfinitePlaces.card_infinitePlace k K
    rw [hcK, hck, ← hn] at h
    exact h
  -- arithmetic: `A + B + B = (a + b) * n + b * n`
  have hexp : A + B + B = (a + b) * n + b * n := by
    have e : A + B + B = (a + 2 * b) * n := by
      calc A + B + B = A + 2 * B := by ring
        _ = Module.finrank ℚ K := hK
        _ = Module.finrank ℚ k * n := hfr
        _ = (a + 2 * b) * n := by rw [← hk]
    rw [e]
    ring
  have hB : B = b * n := by
    rw [← hcard] at hexp
    exact Nat.add_left_cancel hexp
  rw [hB, Nat.mul_comm]

end Commons.NumberTheory.NumberField