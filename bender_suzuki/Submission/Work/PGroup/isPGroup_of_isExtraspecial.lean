import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- An extraspecial `p`-group is a `p`-group.

By definition (`Work.PGroup.IsExtraspecial`) an extraspecial group is in particular *special*
(`hE.2.1`), and the definition of `Work.PGroup.IsSpecial` is a disjunction: either `E` is
elementary abelian of exponent `p`, in which case every element of `E` has order dividing `p`
(`Work.PGroup.IsElementaryAbelian.isPGroup`), or `E` is a `p`-group by the very first conjunct of
the second disjunct. -/
theorem isPGroup_of_isExtraspecial {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hE : Work.PGroup.IsExtraspecial p E) : IsPGroup p E := by
  obtain ⟨-, hspec, -⟩ := hE
  rcases hspec with h | h
  · exact h.isPGroup
  · exact h.1

end Work.PGroup
