import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- The order of an element is invariant under conjugation. -/
theorem orderOf_conj {G : Type*} [Group G] (z t : G) : orderOf (z * t * z⁻¹) = orderOf t := by
  have h : SemiconjBy z t (z * t * z⁻¹) := by
    unfold SemiconjBy
    group
  exact (SemiconjBy.orderOf_eq z (x := t) (y := z * t * z⁻¹) h).symm

end Commons.GroupTheory.StronglyEmbedded