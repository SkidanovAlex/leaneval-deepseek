import Mathlib.GroupTheory.Index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

/-- The cardinality of the left-quotient `G ⧸ H` equals the index of `H`.
This is `Subgroup.index` definitionally, since `H.index` is defined as
`Nat.card (G ⧸ H)` and `G ⧸ H` is `Quotient (QuotientGroup.leftRel H)`. -/
theorem card_quotient_leftRel {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (Quotient (QuotientGroup.leftRel H)) = H.index := by
  rfl

end Commons.GroupTheory.Subgroup