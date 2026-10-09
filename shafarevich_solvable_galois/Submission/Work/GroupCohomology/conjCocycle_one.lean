import Mathlib
import Submission.Work.GroupCohomology.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem conjCocycle_one {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal]
    (f : Work.GroupCohomology.Z1 N A) :
    Work.GroupCohomology.conjCocycle (N := N) 1 f = f := by
  ext n
  simp [conjCocycle_apply, conjAutN]

end Work.GroupCohomology
