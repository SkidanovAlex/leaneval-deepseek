import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- If the normal subgroup `K` contains the `p`-th powers of all elements of `H`, then the
subquotient `H/K` has exponent dividing `p` (it is an elementary abelian `p`-group, together
with `Work.Shrinking.isMulCommutative_subquotient`).

Proof: `QuotientGroup.mk'_surjective` writes `x = mk y` for `y : H` with `(y : P) ^ p ∈ K`, so
`x ^ p = mk (y ^ p) = 1` by `map_pow` and `QuotientGroup.eq_one_iff` /
`Subgroup.mem_subgroupOf`. -/
theorem pow_eq_one_subquotient {P : Type*} [Group P] {H K : Subgroup P} [K.Normal] {p : ℕ}
    (hp : ∀ x ∈ H, x ^ p ∈ K) (x : H ⧸ K.subgroupOf H) : x ^ p = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) x
  rw [← map_pow (QuotientGroup.mk' (K.subgroupOf H)) y p, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hp (y : P) y.2))

end Work.Shrinking
