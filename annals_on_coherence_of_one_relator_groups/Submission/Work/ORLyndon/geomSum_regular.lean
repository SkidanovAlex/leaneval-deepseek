import Mathlib
import Submission.Work.ORLyndon.mul_one_sub_of_infinite_order

/-!
# The finite geometric sum `1 + h + ⋯ + h ^ (k-1)` is a non-zero-divisor

Let `h` be an element of a group `G` whose `k`-th power `h ^ k` has infinite order, and let `K` be a
field.  Then the finite geometric sum

`S = ∑_{i < k} (of h) ^ i = 1 + h + ⋯ + h ^ (k-1)`

in the group algebra `K[G]` is a *right non-zero-divisor*: `c * S = 0` forces `c = 0`.

The proof is the telescoping identity

`S * (1 - h) = 1 - h ^ k`

(`geom_sum_mul_neg`), together with the fact -- proved in
`Work.ORLyndon.mul_one_sub_of_infinite_order` -- that `1 - w` is a right non-zero-divisor in `K[G]`
whenever `orderOf w = 0`.  Indeed, multiplying `c * S = 0` on the right by `1 - h` gives
`c * (1 - h ^ k) = 0`, and `orderOf (h ^ k) = 0` is exactly the hypothesis, so `c = 0`.

Note that no hypothesis on `k` itself is needed: for `k = 0` the hypothesis `orderOf (h ^ k) = 0`
is already contradictory (`h ^ 0 = 1` has order `1`), so the statement is vacuous.  This is the
`k`-th-power version of the geometric-sum regularity used in `Work.ORLyndon.annAt_of_geometric`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The finite geometric sum is right regular.**  If `orderOf (h ^ k) = 0` in a group `G`, then
for any field `K` the geometric sum `∑ i ∈ Finset.range k, (of K G h) ^ i` is a right
non-zero-divisor of `MonoidAlgebra K G`: `c * S = 0` implies `c = 0`. -/
theorem geomSum_regular {G : Type*} [Group G] {K : Type*} [Field K] (h : G) (k : ℕ)
    (hord : orderOf (h ^ k) = 0) (c : MonoidAlgebra K G)
    (hc : c * (∑ i ∈ Finset.range k, (MonoidAlgebra.of K G h) ^ i) = 0) : c = 0 := by
  -- Telescoping: the geometric sum times `1 - h` is `1 - h ^ k`.
  have htel : (∑ i ∈ Finset.range k, (MonoidAlgebra.of K G h) ^ i) *
      (1 - MonoidAlgebra.of K G h) = 1 - MonoidAlgebra.of K G (h ^ k) := by
    rw [geom_sum_mul_neg (MonoidAlgebra.of K G h) k, map_pow]
  -- Multiply `c * S = 0` on the right by `1 - h`.
  have h2 : c * (1 - MonoidAlgebra.of K G (h ^ k)) = 0 := by
    have h3 := congrArg (fun z => z * (1 - MonoidAlgebra.of K G h)) hc
    rw [zero_mul] at h3
    rwa [mul_assoc, htel] at h3
  -- `1 - h ^ k` is a right non-zero-divisor, since `h ^ k` has infinite order.
  exact mul_one_sub_of_infinite_order (K := K) hord c h2

end Work.ORLyndon
