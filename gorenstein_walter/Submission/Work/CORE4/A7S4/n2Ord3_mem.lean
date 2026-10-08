import Mathlib
import Submission.Work.CORE4.A7S4Defs

namespace Work.CORE4.A7S4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem n2Ord3_mem : ∀ k : Equiv.Perm (Fin 7), N2Ord3Cond k → k ∈ n2Ord3 := by decide

end Work.CORE4.A7S4
