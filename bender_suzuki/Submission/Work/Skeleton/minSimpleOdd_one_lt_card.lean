import Mathlib
import Submission.Work.Skeleton.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

theorem minSimpleOdd_one_lt_card {G : Type*} [Group G] [Finite G] (h : MinSimpleOdd G) :
    1 < Nat.card G :=
  Finite.one_lt_card_iff_nontrivial.mpr h.nontrivial

end Work.Skeleton
