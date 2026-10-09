import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **Cardinality detects proper inclusion of subgroups.**  If `H ≤ K` are subgroups of a group
and `K` is finite, then `#H < #K` exactly when `H` is a proper subgroup of `K`.

This is the elementary group-theoretic input to the description of the lower breaks of the
ramification filtration: the filtration `G_i` is decreasing, so a strict drop from `G_i` to
`G_{i+1}` is the same thing as a strict drop of the orders. -/
theorem natCard_lt_natCard_iff_ne {G : Type*} [Group G] {H K : Subgroup G} [Finite K]
    (h : H ≤ K) : Nat.card H < Nat.card K ↔ H ≠ K := by
  refine ⟨fun hlt heq => absurd (heq ▸ hlt) (lt_irrefl _), fun hne => ?_⟩
  rcases lt_or_eq_of_le (Subgroup.card_le_of_le h) with hlt | heq
  · exact hlt
  · exact absurd (Subgroup.eq_of_le_of_card_ge h heq.ge) hne

/-- **Lower breaks are exactly the strict drops of the lower indices.**  Since the ramification
filtration `G_i` is decreasing, `i` is a lower break (i.e. `G_{i+1} ≠ G_i`) if and only if the
order of `G_i` strictly exceeds the order of `G_{i+1}` — the subgroup is proper precisely when
its cardinality is smaller. -/
theorem lowerBreak_iff_lowerIndex_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] (i : ℕ) :
    NK.Ramification.LowerBreak (K := K) A i ↔
      NK.Ramification.lowerIndex (K := K) A (i + 1) <
        NK.Ramification.lowerIndex (K := K) A i := by
  have hle := ramificationSubgroup_le_ramificationSubgroup (K := K) A (Nat.le_succ i)
  rw [LowerBreak, ne_comm, lowerIndex, lowerIndex]
  exact (natCard_lt_natCard_iff_ne hle).symm

end NK.Ramification
