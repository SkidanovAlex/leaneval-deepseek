import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- The Frattini subgroup of a finite group is contained in its Fitting subgroup:
`Φ(G)` is characteristic (hence normal) and nilpotent, so it is one of the normal
nilpotent subgroups whose supremum is `F(G)`. -/
theorem frattini_le_fitting (G : Type*) [Group G] [Finite G] :
    frattini G ≤ Work.Fitting.fitting G :=
  le_fitting inferInstance frattini_nilpotent

end Work.Fitting
