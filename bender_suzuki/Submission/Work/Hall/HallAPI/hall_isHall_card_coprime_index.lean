import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.PiNat.hall_coprime_of_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.HallAPI

/-- The order of a Hall `π`-subgroup `H` is coprime to its index `[G : H]`:
`|H|` is a `π`-number and `[G : H]` is a `π'`-number, and a common prime divisor would lie
both in `π` and in its complement. -/
theorem hall_isHall_card_coprime_index {G : Type*} [Group G] [Finite G] {π : ℕ → Prop}
    {H : Subgroup G} (h : Work.Hall.IsHall π H) : (Nat.card H).Coprime H.index := by
  have hm0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hn0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact Work.Hall.PiNat.hall_coprime_of_isPiNat h.1 h.2 hm0 hn0

end Work.Hall.HallAPI
