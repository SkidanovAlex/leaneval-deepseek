import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.Transport

theorem hall_map_subtype_comap_of_le {G : Type*} [Group G] {X H : Subgroup G} (hH : H ≤ X) :
    (H.comap X.subtype).map X.subtype = H :=
  Subgroup.map_comap_eq_self (hH.trans (le_of_eq X.range_subtype.symm))

end Work.Hall.Transport
