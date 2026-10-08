import Mathlib.GroupTheory.Subgroup.Simple

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.IsSimpleGroup

/-- Simplicity is invariant under group isomorphism. -/
theorem of_mulEquiv {G : Type*} {H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsSimpleGroup G) : IsSimpleGroup H :=
  @MulEquiv.isSimpleGroup H _ G _ h e.symm

end Commons.GroupTheory.IsSimpleGroup