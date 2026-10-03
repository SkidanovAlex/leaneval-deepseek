import Mathlib

/-!
# The fibre of the product map over a box of integers

For a nonzero integer `P`, a natural number `k` and a bound `m`, the number of `k`-tuples
`l : Fin k → ℤ` with `l i ∈ [-m, m]` for all `i` and `∏ i, l i = P` is at most
`d(|P|)^k · 2^k`, where `d(|P|) = P.natAbs.divisors.card` is the number of positive divisors
of `|P|`.

The point is that the bound is completely independent of `m`: every entry `l i` of such a tuple
is a **divisor of `P`** (because `P = l i · ∏_{j ≠ i} l j`) and is nonzero, so the fibre is a
subset of the `k`-tuples drawn from the set `Int.divisors P` of all integer divisors of `P`,
which has at most `2 · d(|P|)` elements.  Hence

  `#fibre ≤ (Int.divisors P).card ^ k ≤ (2 · d(|P|)) ^ k = d(|P|)^k · 2^k`.

This is the purely combinatorial input of the "level set / fibre counting" step in the
circle-method treatment of Weyl sums: for a fixed nonzero product `P` there are only
`O(d(|P|)^k)` tuples realising it.
-/

namespace Work.A3.Weil

open Finset
open scoped BigOperators

/-- The set of integer divisors of `P` has at most `2 * P.natAbs.divisors.card` elements: it is
the (disjoint) union of the positive divisors `d` of `|P|` and their negatives `-d`. -/
lemma card_intDivisors_le_two_mul (P : ℤ) :
    (Int.divisors P).card ≤ 2 * P.natAbs.divisors.card := by
  rw [Int.divisors, Finset.card_disjUnion]
  simp [Finset.card_map, two_mul]

/-- **Fibre count for the product map over a box.**  For `P ≠ 0`, the number of `k`-tuples of
integers in `[-m, m]` whose product is `P` is at most `d(|P|)^k · 2^k`, where `d(|P|)` is the
number of positive divisors of `|P|`.  In particular the bound does not depend on `m`. -/
theorem card_fiber_le_pow_divisors (k m : ℕ) (P : ℤ) (hP : P ≠ 0) :
    ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
      (fun l => ∏ i, l i = P)).card ≤ ((P.natAbs).divisors.card) ^ k * 2 ^ k := by
  classical
  -- Every tuple in the fibre consists of divisors of `P`, hence lies in `(Int.divisors P)^k`.
  have hsub : ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
      (fun l => ∏ i, l i = P)) ⊆ Fintype.piFinset (fun _ : Fin k => Int.divisors P) := by
    intro l hl
    rw [Finset.mem_filter] at hl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Int.mem_divisors]
    refine ⟨?_, hP⟩
    rw [← hl.2]
    exact Finset.dvd_prod_of_mem l (Finset.mem_univ i)
  calc ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
        (fun l => ∏ i, l i = P)).card
      ≤ (Fintype.piFinset (fun _ : Fin k => Int.divisors P)).card := Finset.card_le_card hsub
    _ = (Int.divisors P).card ^ k := by rw [Fintype.card_piFinset]; simp
    _ ≤ (2 * P.natAbs.divisors.card) ^ k := Nat.pow_le_pow_left (card_intDivisors_le_two_mul P) k
    _ = P.natAbs.divisors.card ^ k * 2 ^ k := by rw [mul_pow, mul_comm]

end Work.A3.Weil
