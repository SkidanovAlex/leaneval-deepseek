import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

/-- The image of an intersection is the intersection of the images, provided the
kernel of `φ` is contained in the first subgroup. -/
theorem map_inf_eq_map_inf_map_of_ker_le {G H : Type*} [Group G] [Group H]
    (φ : G →* H) {H₁ H₂ : Subgroup G} (hker : φ.ker ≤ H₁) :
    (H₁ ⊓ H₂).map φ = H₁.map φ ⊓ H₂.map φ :=
  map_inf_eq_of_ker_le φ H₁ H₂ hker

end Commons.GroupTheory.Subgroup
