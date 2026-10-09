import Mathlib
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem H1_induction_on {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] {C : Work.GroupCohomology.H1 G A → Prop} (x : Work.GroupCohomology.H1 G A)
    (h : ∀ f : Work.GroupCohomology.Z1 G A, C (Work.GroupCohomology.H1π G A f)) : C x := by
  obtain ⟨f, rfl⟩ :=
    QuotientAddGroup.mk'_surjective ((B1 G A).comap (Z1 G A).subtype) x
  exact h f

end Work.GroupCohomology
