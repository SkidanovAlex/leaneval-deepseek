import Mathlib
import Submission.Diff.Grad
import Submission.Diff.Interfaces
import Submission.GlobalBM
import Submission.HopfRinow2
import Submission.CutTime
import Submission.Work.Diff.L.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Re-export module for the `spread_scalar` area (`Work.Diff.L`): the frozen interfaces, the
seeded Jacobi/Bonnet–Myers/comparison library and the local `Defs` of this area. Importing this
module gives a delegated lemma everything the statements below mention. -/
