import Submission.ZagierHoffmanProof.CarlitzExpLog

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Carlitz exponential/logarithm inverse laws
-/

namespace ZagierHoffmanPositiveChar

section Reg

open PowerSeries

attribute [local instance 100] Classical.decEq

/-- ★ `e_C(log_C z) = z` over `F₂`. -/
example : (carlitzExp (ZMod 2)).subst (carlitzLog (ZMod 2)) = PowerSeries.X :=
  carlitzExp_subst_log _

/-- ★ `log_C(e_C z) = z` over `F₃`. -/
example : (carlitzLog (ZMod 3)).subst (carlitzExp (ZMod 3)) = PowerSeries.X :=
  carlitzLog_subst_exp _

/-- Both inverse laws over `F₂`. -/
example : (carlitzLog (ZMod 2)).subst (carlitzExp (ZMod 2)) = PowerSeries.X
    ∧ (carlitzExp (ZMod 2)).subst (carlitzLog (ZMod 2)) = PowerSeries.X :=
  carlitzLog_exp_inverse _

end Reg

end ZagierHoffmanPositiveChar
