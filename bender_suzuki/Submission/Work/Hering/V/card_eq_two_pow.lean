import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = Inv(G) ∪ {1}` has cardinality a power of two

For a finite group `G` of 2-rank `≥ 2` acting doubly transitively by conjugation on its
involutions, the set `V = Inv(G) ∪ {1}` is a subgroup (`Work.Hering.invSubgroup`), and it is
elementary abelian: every element has order dividing `2`. In particular `V` is a finite
2-group, so its cardinality is a power of `2`.

This is the elementary observation underlying the description of `V` as a vector space over
`𝔽₂` in Peterfalvi I §2.
-/

set_option autoImplicit false

namespace Work.Hering.V

/-- `V = Inv(G) ∪ {1}` has cardinality `2 ^ m` for some `m`: it is a finite 2-group
(`Work.Hering.isPGroup_invSubgroup`), and a finite `p`-group has cardinality a power of `p`
(`IsPGroup.iff_card`). -/
theorem card_eq_two_pow {G : Type*} [Group G] (hDT : DTInv G) (h4 : HasFourGroup G) [Finite G] :
    ∃ m : ℕ, Nat.card ↥(invSubgroup hDT h4) = 2 ^ m := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(invSubgroup hDT h4))).mp
    (isPGroup_invSubgroup hDT h4)
  exact ⟨n, hn⟩

end Work.Hering.V
