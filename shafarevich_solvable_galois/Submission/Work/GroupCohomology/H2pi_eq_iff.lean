import Mathlib
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem H2pi_eq_iff {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (c c' : Work.GroupCohomology.Z2 G A) :
    Work.GroupCohomology.H2π G A c = Work.GroupCohomology.H2π G A c' ↔
      ((c - c' : Work.GroupCohomology.Z2 G A) : (G × G) → A) ∈ Work.GroupCohomology.B2 G A := by
  unfold H2π
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_comap]
  rfl

end Work.GroupCohomology
