import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The relative index of a Hall subgroup in an overgroup is a `π'`-number

If `H ≤ K ≤ G` and `H` is a Hall `π`-subgroup of `G`, then `[K : H] = H.relIndex K` is a
`π'`-number.  Indeed the tower law `H.relIndex K * K.index = H.index` exhibits `H.relIndex K`
as a divisor of `H.index`, which is a `π'`-number because `H` is Hall, and a divisor of a
`π'`-number is again a `π'`-number.
-/

namespace Work.Hall.HallAPI

theorem hall_isHall_relIndex {G : Type*} [Group G] [Finite G] {π : ℕ → Prop} {H K : Subgroup G}
    (hH : Work.Hall.IsHall π H) (h : H ≤ K) :
    Work.Hall.IsPiNat (fun p => ¬ π p) (H.relIndex K) :=
  fun p hp hpdvd => hH.2 p hp (hpdvd.trans (Subgroup.relIndex_dvd_index_of_le h))

end Work.Hall.HallAPI
