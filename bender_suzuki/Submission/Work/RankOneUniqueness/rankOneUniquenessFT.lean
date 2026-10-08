import Submission.Work.RankOneUniqueness.rankOneUniqueness

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.rankOneUniquenessFT` — the area theorem in `FeitThompsonProp` form

The convention for the areas of this project is `theorem <Area> (hFT : FeitThompsonProp)
(h… : …Prop) : <AreaProp>`.  The rank-one uniqueness lemma needs no character theory at all
(its proof is group-theoretic), so the Feit–Thompson hypothesis is simply ignored.
-/

set_option autoImplicit false

namespace Work.RankOneUniqueness

/-- `RankOneUniquenessProp`, with the (unused) `FeitThompsonProp` hypothesis of the convention. -/
theorem rankOneUniquenessFT (_hFT : Submission.Blueprint.FeitThompsonProp) :
    Submission.Blueprint.RankOneUniquenessProp := rankOneUniqueness

end Work.RankOneUniqueness
