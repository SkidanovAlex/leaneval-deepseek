import Submission.Work.GlaubermanZJ.pstable_of_abelianSylowTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# "Abelian Sylow 2-subgroups" passes to quotients

This module re-exports
`Work.GlaubermanZJ.hasAbelianSylowTwo_quotient : HasAbelianSylowTwo G → HasAbelianSylowTwo (G ⧸ N)`,
which is proved in `Submission.Work.GlaubermanZJ.pstable_of_abelianSylowTwo`.
-/
