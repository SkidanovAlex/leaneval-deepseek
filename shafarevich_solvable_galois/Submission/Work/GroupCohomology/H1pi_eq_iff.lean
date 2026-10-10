import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem H1pi_eq_iff {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (f f' : Work.GroupCohomology.Z1 G A) :
    Work.GroupCohomology.H1π G A f = Work.GroupCohomology.H1π G A f' ↔
      ((f - f' : Work.GroupCohomology.Z1 G A) : G → A) ∈ Work.GroupCohomology.B1 G A := by
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  exact Iff.rfl

end Work.GroupCohomology
