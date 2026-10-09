import Mathlib
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- `H¹(G, A)` is the quotient of `Z¹` by `B¹`, so the class of a cocycle `f` is zero if and only
if `f` is a coboundary. -/
theorem H1pi_eq_zero_iff {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (f : Work.GroupCohomology.Z1 G A) :
    Work.GroupCohomology.H1π G A f = 0 ↔ (f : G → A) ∈ Work.GroupCohomology.B1 G A := by
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  rfl

end Work.GroupCohomology
