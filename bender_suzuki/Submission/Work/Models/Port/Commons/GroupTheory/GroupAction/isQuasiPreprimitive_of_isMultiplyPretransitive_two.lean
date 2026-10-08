import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

/-- A `2`-pretransitive action is quasipreprimitive: it is preprimitive
(Wielandt), and preprimitive actions are quasipreprimitive. -/
theorem isQuasiPreprimitive_of_isMultiplyPretransitive_two {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] (h : MulAction.IsMultiplyPretransitive G X 2) :
    MulAction.IsQuasiPreprimitive G X :=
  letI : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h
  inferInstance

end Commons.GroupTheory.GroupAction