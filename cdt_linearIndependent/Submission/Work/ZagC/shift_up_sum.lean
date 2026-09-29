import Mathlib

/-!
# Reindexing the `m ↦ m+1` (up-shift) binomial sum

For any `v : ℕ → ℚ` and `n : ℕ`,

  `Σ_{m ≤ n+1} C(n,m)(m+1)² v_{m+1} = Σ_{j ≤ n+1} j² C(n,j−1) v_j`.

Both sides equal the reindexed sum `Σ_{j=1}^{n+1} j² C(n,j−1) v_j`: the term at `m`
is the term at `j = m+1`, and the two boundary terms `j = 0` on the right and
`j = n+2` on the left both vanish (the latter because `C(n,n+1) = 0`).

This is the `Y2`-level "shift up" identity used in the `cₙ` integrality argument.
-/

namespace Work.ZagC

theorem shift_up_sum (v : ℕ → ℚ) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 2), (n.choose m : ℚ) * ((m : ℚ) + 1) ^ 2 * v (m + 1))
      = ∑ j ∈ Finset.range (n + 2), (j : ℚ) ^ 2 * (n.choose (j - 1) : ℚ) * v j := by
  -- Rewrite the left-hand summand at `m` as the right-hand summand at `m + 1`.
  have hL : (∑ m ∈ Finset.range (n + 2), (n.choose m : ℚ) * ((m : ℚ) + 1) ^ 2 * v (m + 1))
      = ∑ m ∈ Finset.range (n + 2),
          (((m + 1 : ℕ)) : ℚ) ^ 2 * (n.choose ((m + 1) - 1) : ℚ) * v (m + 1) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hL]
  -- The two boundary terms `j = 0` and `j = n+2` both vanish.
  have hzero : (((0 : ℕ)) : ℚ) ^ 2 * (n.choose (0 - 1) : ℚ) * v 0 = 0 := by simp
  have htop : ((((n + 1) + 1 : ℕ)) : ℚ) ^ 2 * (n.choose (((n + 1) + 1) - 1) : ℚ)
      * v ((n + 1) + 1) = 0 := by
    rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp
  -- Peel off the last term on the left (`Finset.sum_range_succ`) and the first
  -- term on the right (`Finset.sum_range_succ'`); the shifted middle sums coincide.
  conv_lhs => rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ']
  rw [htop, hzero]

end Work.ZagC
