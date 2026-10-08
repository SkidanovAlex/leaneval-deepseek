import Mathlib
import Submission.Work.CORE4.A7S4Defs

namespace Work.CORE4.A7S4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem n1Inv_mem : ∀ s : Equiv.Perm (Fin 7), N1InvCond s → s ∈ n1Inv := by decide

end Work.CORE4.A7S4
