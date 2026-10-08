import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isQuasiPreprimitive_of_isMultiplyPretransitive_two
import Submission.Work.Models.Port.Commons.GroupTheory.Iwasawa.iwasawaStructure_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SpecificGroups.PSL2_isPerfect

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.SL2

theorem isSimpleGroup_projectiveSpecialLinearGroup {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : 4 ≤ Nat.card F) : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF

end Commons.GroupTheory.SL2