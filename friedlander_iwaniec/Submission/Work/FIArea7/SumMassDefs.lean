/-
# `Submission.Work.FIArea7.SumMassDefs` — the vocabulary of the `π`-sublattice mass bound

The estimate `Work.FIArea7.sum_massW_le` bounds the total mass of the coefficient `β` on the
`π`-sublattices, `∑_{π ∈ bigPi Pa m} massW Pa β π m`, by the total mass `∑_{z ∈ gBox radN} ‖β z‖²`
times `4 log (N+2)`.  The argument groups the pairs `(π, w)` of the double sum by the point
`z = π * w`: each `z` of the box can be reached only through the primes `π ∈ bigPi Pa m` that
divide `z`, and there are at most `4 log (N+2)` of them (each such `π` has `gnorm π > Pa.Pz ≥ 2`,
and the pairwise non-associate primes dividing `z` have a product of norms dividing `gnorm z`).

This module holds the one piece of vocabulary that statement needs — the finset `bigPiDvd Pa m z`
of the primes of `bigPi Pa m` dividing `z` — together with its two membership lemmas, so that the
delegated lemmas can be stated without any `DecidablePred` instance at the use site.

The two mathematical inputs of that argument, spelled out:

* **Multiplicity.**  For `z ≠ 0` the pairs `(π, w)` with `π * w = z`, `π ∈ bigPi Pa m`, are indexed
  by the set `bigPiDvd Pa m z` of primes of `bigPi Pa m` dividing `z`: `w = z / π` is forced.  The
  lemma `sum_massW_fiber_le` converts the double sum over `π` and `piBox` into a sum over `z` of
  `(bigPiDvd Pa m z).card * ‖β z‖²`.
* **Counting.**  Two elements of `bigPi` are *never* associates: both are primes with `0 < re` and
  `0 ≤ im`, and the four units `±1, ±i` force an associate of such an element to be equal to it.
  Hence the elements of `bigPiDvd Pa m z` are pairwise non-associate primes of `ℤ[i]` dividing `z`,
  so their product divides `z` (by induction: a prime dividing `z` and not dividing a factor of the
  product is coprime to it, hence divides the cofactor), whence

    `∏_{π ∈ bigPiDvd Pa m z} gnorm π ∣ gnorm z`

  and in particular `∏_{π ∈ bigPiDvd Pa m z} gnorm π ≤ gnorm z`.  Since `Pa.Pz < gnorm π` with
  `2 ≤ Pa.Pz`, all `card (bigPiDvd Pa m z)` factors are `≥ 3`; so `3 ^ card ≤ gnorm z ≤ 2 * Pa.N`,
  and taking logarithms of the two ends gives `card ≤ 4 log (N+2)`.  This is `card_bigPi_dvd_le`.
-/
import Mathlib
import Submission.Work.FIArea7.PiPairDefs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The primes of `bigPi Pa m` dividing `z`**: the possible `π` of a pair `(π, w)` with
`π * w = z`.  This is the multiplicity with which a point `z` of the box is counted in
`∑_{π ∈ bigPi Pa m} massW Pa β π m`. -/
def bigPiDvd (Pa : Work.FITop.Params) (m : ℕ) (z : GaussianInt) : Finset GaussianInt :=
  (Work.FIArea7.bigPi Pa m).filter (fun π => π ∣ z)

/-- Membership in `bigPi`, unfolded. -/
lemma mem_bigPi {Pa : Work.FITop.Params} {m : ℕ} {π : GaussianInt} :
    π ∈ bigPi Pa m ↔ π ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) ∧ Prime π ∧ 0 < π.re
      ∧ 0 ≤ π.im ∧ Pa.Pz < Work.FIPlan.gnorm π ∧ Nat.Coprime (Work.FIPlan.gnorm π) m := by
  simp only [bigPi, Finset.mem_filter]

/-- Membership in `bigPiDvd`, unfolded. -/
lemma mem_bigPiDvd {Pa : Work.FITop.Params} {m : ℕ} {z π : GaussianInt} :
    π ∈ bigPiDvd Pa m z ↔ π ∈ bigPi Pa m ∧ π ∣ z := by
  simp only [bigPiDvd, Finset.mem_filter]

end

end Work.FIArea7
