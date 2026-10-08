import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.commutator_le_omega1_aux
import Submission.Work.Higman.center_eq_omega1_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

/-- In a Suzuki 2-group the commutator subgroup equals the centre
(Higman 1963, §2: `Ω₁(P) = Z(P) = Φ(P) = P'`). -/
theorem commutator_eq_center {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    commutator P = Subgroup.center P := by
  apply le_antisymm
  · exact (commutator_le_omega1_aux h).trans h.omega1_le_center
  · rw [center_eq_omega1_aux h]
    exact omega1_le_commutator h

end Work.Higman
