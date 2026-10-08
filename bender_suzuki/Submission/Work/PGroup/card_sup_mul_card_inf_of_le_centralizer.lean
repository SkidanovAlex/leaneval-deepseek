import Mathlib
import Submission.Work.PGroup.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- For subgroups `H K` of a group `G` with `K` contained in the centralizer of `H`, the join
and the intersection satisfy `|H ⊔ K| * |H ⊓ K| = |H| * |K|`.

This is the elementwise-commuting product formula `Work.PGroup.card_sup_mul_card_inf` applied to
the commutation relation `h * k = k * h` that the hypothesis `K ≤ C_G(H)` provides. -/
theorem card_sup_mul_card_inf_of_le_centralizer {G : Type*} [Group G] {H K : Subgroup G}
    [Finite ↥H] [Finite ↥K] (h : K ≤ Subgroup.centralizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  apply card_sup_mul_card_inf H K
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.mp (h hb) a ha

end Work.PGroup
