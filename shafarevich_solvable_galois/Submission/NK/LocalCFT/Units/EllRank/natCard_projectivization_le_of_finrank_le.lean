import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Monotonicity of the cardinality of a projective space in the dimension

For a finite field `k` and `k`-vector spaces `M`, `N`, the number of points of the
projective space `ℙ k M` is `∑_{i < finrank k M} (Nat.card k) ^ i`
(`Projectivization.card_of_finrank`).  This is monotone in the dimension, since the
partial geometric sums of a base `≥ 1` are increasing.  Hence `finrank k M ≤ finrank k N`
implies `Nat.card (ℙ k M) ≤ Nat.card (ℙ k N)`.

No finiteness hypothesis on `M`, `N` is needed: when a space is infinite-dimensional its
`finrank` is `0` and its projectivization is infinite, so both sides of the formula
degenerate consistently.
-/

namespace NK.LocalCFT.Units.EllRank

/-- **Monotonicity of the number of points of a projective space.**  Over a finite field
`k`, the cardinality of the projective space of a `k`-vector space is nondecreasing in the
`k`-dimension. -/
theorem natCard_projectivization_le_of_finrank_le (k : Type*) [Field k] [Finite k] (M N : Type*)
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (h : Module.finrank k M ≤ Module.finrank k N) :
    Nat.card (Projectivization k M) ≤ Nat.card (Projectivization k N) := by
  rw [Projectivization.card_of_finrank (k := k) (V := M) rfl,
    Projectivization.card_of_finrank (k := k) (V := N) rfl]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => Nat.zero_le _)

end NK.LocalCFT.Units.EllRank
