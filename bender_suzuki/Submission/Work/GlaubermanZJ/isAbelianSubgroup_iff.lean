import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-- The blueprint's elementwise abelianness predicate for a subgroup agrees with
`IsMulCommutative` on the subgroup viewed as a group.

The forward direction sends `x y ∈ A` to the elements `⟨x, hx⟩ ⟨y, hy⟩` of `↥A` and
extracts the equality of the underlying elements; the backward direction pushes an
equality in `↥A` down to `G` with `congrArg Subtype.val`. -/
theorem isAbelianSubgroup_iff {G : Type*} [Group G] {A : Subgroup G} :
    Submission.Blueprint.IsAbelianSubgroup A ↔ IsMulCommutative ↥A := by
  rw [Submission.Blueprint.IsAbelianSubgroup, isMulCommutative_iff]
  constructor
  · intro h a b
    exact Subtype.ext (h a.1 a.2 b.1 b.2)
  · intro h x hx y hy
    exact congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)

end Work.GlaubermanZJ
