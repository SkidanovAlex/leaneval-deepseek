import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

theorem hasAbelianSylowTwo_iff {G : Type*} [Group G] :
    Work.GlaubermanZJ.HasAbelianSylowTwo G ↔
      ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G) := by
  constructor
  · intro h Q
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact h Q a.1 a.2 b.1 b.2
  · intro h Q x hx y hy
    have hc := (h Q).is_comm.comm (⟨x, hx⟩ : ↥(Q : Subgroup G)) ⟨y, hy⟩
    have hv := Subtype.ext_iff.mp hc
    simpa only [Subtype.coe_mk, Subgroup.coe_mul] using hv

end Work.GlaubermanZJ
