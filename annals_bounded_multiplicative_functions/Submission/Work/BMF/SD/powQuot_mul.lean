import Mathlib
import Submission.Work.BMF.SD.powQuot_def

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The identity `q * powQuot n q j = (n+q)^j - n^j`

`powQuot n q j = ∑_{i<j} (n+q)^i n^{j-1-i}` is the explicit integral representative of
`((n+q)^j - n^j)/q` introduced in `Work.BMF.SD.powQuot_def`.  This file records the
defining identity, which is the two-variable geometric-sum identity
`Commute.mul_geom_sum₂` for `x = n+q`, `y = n` together with `x - y = q`.
-/

namespace Work.BMF.SD

theorem powQuot_mul (n q j : ℕ) :
    (q : ℤ) * Work.BMF.SD.powQuot n q j = ((n : ℤ) + (q : ℤ)) ^ j - (n : ℤ) ^ j := by
  rw [powQuot]
  rw [← (Commute.all ((n : ℤ) + (q : ℤ)) (n : ℤ)).mul_geom_sum₂ j]
  ring

end Work.BMF.SD
