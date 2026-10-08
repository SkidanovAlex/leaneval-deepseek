import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.Transport.hall_card_comap_subtype_of_le
import Submission.Work.Hall.HallAPI.hall_isHall_relIndex

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Hall subgroups pull back along an inclusion of subgroups

If `H ≤ X ≤ G` and `H` is a Hall `π`-subgroup of `G`, then `H`, viewed as a subgroup of `X`
via `X.subtype`, is a Hall `π`-subgroup of `X`.

The order part is `|H.comap X.subtype| = |H|` (`hall_card_comap_subtype_of_le`), and the index
part is the relative index `H.relIndex X = [X : H]`, a divisor of the index `[G : H]`
(`hall_isHall_relIndex`).
-/

namespace Work.Hall.Transport

theorem hall_isHall_comap_subtype {G : Type*} [Group G] [Finite G] {X H : Subgroup G} {π : ℕ → Prop}
    (hH : H ≤ X) (h : Work.Hall.IsHall π H) :
    Work.Hall.IsHall π (H.comap X.subtype) := by
  constructor
  · rw [hall_card_comap_subtype_of_le hH]
    exact h.1
  · have hidx : (H.comap X.subtype).index = H.relIndex X := rfl
    rw [hidx]
    exact Work.Hall.HallAPI.hall_isHall_relIndex h hH

end Work.Hall.Transport
