import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Hall subgroups descend to quotients by `π`-normal subgroups

If `N ◁ G` has `π`-number order and `H ≤ G` is a Hall `π`-subgroup, then the image of `H`
in `G ⧸ N` is again a Hall `π`-subgroup.

Both halves are immediate from divisibility: the order of the image divides `|H|`
(`Subgroup.card_map_dvd`), and, `mk' N` being surjective, the index of the image divides `[G : H]`
(`Subgroup.index_map_dvd`); a divisor of a `π`-number is a `π`-number.
-/

namespace Work.Hall.HallAPI

set_option linter.unusedVariables false in
theorem hall_isHall_map_mk {G : Type*} [Group G] {π : ℕ → Prop} {N H : Subgroup G} [N.Normal]
    (hN : Work.Hall.IsPiNat π (Nat.card N)) (h : Work.Hall.IsHall π H) :
    Work.Hall.IsHall π (H.map (QuotientGroup.mk' N)) := by
  constructor
  · -- `|H · N / N|` divides `|H|`, hence is a `π`-number
    intro p hp hpdvd
    exact h.1 p hp (hpdvd.trans (Subgroup.card_map_dvd H (QuotientGroup.mk' N)))
  · -- `[G ⧸ N : H · N / N]` divides `[G : H]`, hence is a `π'`-number
    intro p hp hpdvd
    exact h.2 p hp (hpdvd.trans (Subgroup.index_map_dvd H (QuotientGroup.mk'_surjective N)))

end Work.Hall.HallAPI
