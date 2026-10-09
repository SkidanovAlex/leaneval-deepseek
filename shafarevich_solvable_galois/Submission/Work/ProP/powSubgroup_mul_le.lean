import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- Iterating the `p`-th power subgroup: `H^(p*q) ≤ (H^q)^p`, i.e.
`powSubgroup (p*q) H ≤ powSubgroup p (powSubgroup q H)`.

Proof: every generator `x ^ (p*q) = (x ^ q) ^ p` of the left-hand side lies in
`powSubgroup p (powSubgroup q H)` because `x ^ q ∈ powSubgroup q H`; conclude with
`Subgroup.closure_le` and `Subgroup.subset_closure`. -/
theorem powSubgroup_mul_le (p q : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    Work.Shrinking.powSubgroup (p * q) H ≤
      Work.Shrinking.powSubgroup p (Work.Shrinking.powSubgroup q H) := by
  rw [Work.Shrinking.powSubgroup, Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨y ^ q, Subgroup.subset_closure ⟨y, hy, rfl⟩, ?_⟩
  show (y ^ q) ^ p = y ^ (p * q)
  rw [← pow_mul, mul_comm]

end Work.ProP
