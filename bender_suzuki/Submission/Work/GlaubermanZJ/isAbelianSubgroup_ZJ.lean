import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-- `Z(J(P)) = J(P) ∩ C_G(J(P))` is abelian: every element of `ZJ P` lies in both `J(P)` and
its centralizer, so any two elements of `ZJ P` commute. -/
theorem isAbelianSubgroup_ZJ {G : Type*} [Group G] (P : Subgroup G) :
    Submission.Blueprint.IsAbelianSubgroup (Submission.Blueprint.ZJ P) := by
  intro x hx y hy
  simp only [Submission.Blueprint.ZJ, Subgroup.mem_inf] at hx hy
  exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm

end Work.GlaubermanZJ
