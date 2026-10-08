import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- A special `p`-group is a `p`-group: if `E` is elementary abelian of exponent `p` this is
immediate (every element has order dividing `p`), and otherwise `IsPGroup p E` is one of the
defining conjuncts of `IsSpecial`. -/
theorem isPGroup_of_isSpecial {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hE : Work.PGroup.IsSpecial p E) : IsPGroup p E :=
  hE.elim IsElementaryAbelian.isPGroup fun h => h.1

end Work.PGroup
