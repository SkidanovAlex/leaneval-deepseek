/-
# `Submission.Work.FIArea7.smallCInner2EpsAux.isSepPairKKUnique`

The total number of prime factors `k` in the *FI* §24 fixed-`k` separation condition
`IsSepPairK r k d m n` is determined by `(r, d, m, n)`: it is the length of the (unique)
decreasing enumeration of the prime factors of `d·m·n`.  Equivalently, the map
`k ↦ IsSepPairK r k d m n` has at most one `k` in its support, which is what lets a sum
`Σ_k (indicator of IsSepPairK r k d m n)` be identified with a single term.

The proof is immediate from uniqueness of the decreasing prime list of a given product
(`Work.FIArea7.IsPrimeList.eq_of_eq`): both hypotheses supply a `StrictAnti` list of primes of
length `k` resp. `k'` and product `d·m·n`, and uniqueness gives `k = k'`.
(No hypothesis on `r` is needed; in particular nothing is assumed about `r ≥ 2`.)
-/
import Mathlib
import Submission.Work.FIArea7.sepPair_eq_of_prod_eq
import Submission.Work.FIArea7.prop172defs

namespace Work.FIArea7.smallCInner2EpsAux

theorem isSepPairKKUnique {r k k' d m n : ℕ}
    (h : Work.FIArea7.IsSepPairK r k d m n) (h' : Work.FIArea7.IsSepPairK r k' d m n) :
    k = k' := by
  obtain ⟨p, hp, -⟩ := h
  obtain ⟨p', hp', -⟩ := h'
  obtain ⟨hc, -⟩ := Work.FIArea7.IsPrimeList.eq_of_eq hp hp'
  exact hc

end Work.FIArea7.smallCInner2EpsAux
