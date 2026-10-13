import Mathlib.Tactic.MinImports
import Submission.Work.FTS.BSIdent.Weyl
import Submission.Work.FTS.PressureOn.weyl_pair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

/-- The Weyl/Liouville pair lemma, as a named input for route C of the identification.
This is verbatim the statement of `Work.FTS.PressureOn.weyl_pair`, which is proved in that area
(`Submission/Work/FTS/PressureOn/weyl_pair.lean`), so the principle follows by direct
instantiation. -/
theorem weylPairPrinciple : Work.FTS.BSIdent.WeylPairPrinciple :=
  Work.FTS.PressureOn.weyl_pair

end Work.FTS.BSIdent.Weyl
