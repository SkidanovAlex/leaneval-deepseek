import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `C_G(K/H)` is antitone in the section: if `K' ≤ K` then every element centralizing
the larger section `K/H` also centralizes the smaller one `K'/H`. -/
theorem sectionCentralizer_antitone_right {G : Type*} [Group G] {H K K' : Subgroup G}
    [H.Normal] (h : K' ≤ K) :
    Work.Fitting.sectionCentralizer H K ≤ Work.Fitting.sectionCentralizer H K' := by
  unfold Work.Fitting.sectionCentralizer
  exact Subgroup.comap_mono (Subgroup.centralizer_le (Subgroup.map_mono h))

end Work.Fitting
