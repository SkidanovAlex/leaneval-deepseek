import Mathlib
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FMap

theorem torusAct_mul {E : Type*} [Field E] [FrobeniusInvolution E] (a b : Eˣ) (p : SZ E) :
    SZ.torusAct a (SZ.torusAct b p) = SZ.torusAct (a * b) p := by
  ext <;> simp only [SZ.torusAct_x, SZ.torusAct_y, Units.val_mul, map_mul] <;> ring

end Work.PSU3.FMap
