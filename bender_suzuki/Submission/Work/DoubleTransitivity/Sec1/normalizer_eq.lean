import Mathlib
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.DoubleTransitivity.Sec1

/-- **Peterfalvi I §1 (2)**, the case `X = H`: a Bender subgroup is its own normaliser.

`H ≤ N_G(H)` holds for every subgroup; the reverse inclusion is
`IsBenderFor.normalizer_le` applied to `X = H`, whose order is divisible by `p = 2`
precisely by the defining property of a Bender subgroup. -/
theorem normalizer_eq {G : Type} [Group G] {H : Subgroup G} (hH : IsBender H) :
    Subgroup.normalizer (H : Set G) = H := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  exact hH.normalizer_le le_rfl hH.1

end Work.DoubleTransitivity.Sec1
