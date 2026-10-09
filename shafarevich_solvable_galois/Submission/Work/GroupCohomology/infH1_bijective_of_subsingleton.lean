import Mathlib
import Submission.Work.GroupCohomology.ker_infH1_eq_bot
import Submission.Work.GroupCohomology.range_infH1_eq_ker_resH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- **Inflation is an isomorphism when the lower cohomology vanishes.**  For `N ◁ G` and a `G`-module `A` with `H¹(N, A) = 0`, the inflation map `H¹(G ⧸ N, A^N) → H¹(G, A)` is bijective. -/
theorem infH1_bijective_of_subsingleton {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] [Subsingleton (H1 N A)] :
    Function.Bijective (Work.GroupCohomology.infH1 (A := A) N) := by
  refine ⟨?_, ?_⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff]
    exact ker_infH1_eq_bot N
  · rw [← AddMonoidHom.range_eq_top, range_infH1_eq_ker_resH1]
    ext x
    simp only [AddSubgroup.mem_top, AddMonoidHom.mem_ker, iff_true]
    exact Subsingleton.elim _ _

end Work.GroupCohomology
