import Submission.ZagierHoffmanProof.StepK33
import Submission.ZagierHoffmanProof.StepK16

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K34: UNCONDITIONAL closure of the R1/ID2/power-sum chain

With `EvalU_all` (StepK33, Thakur's evaluation `U_e·ℓ_e = 1` at every level), the
StepK16 theorems become unconditional:
  ★ R1_all_unc : ∀ d, R1Prop F d          (paper (2.8): S_d(q)+D1·S_{d+1}(1,q−1) = 0)
  ★ ID2_all_unc : ∀ d, 1 ≤ d → ID2 F d
  P_oneExp_unc : ∀ d, P F d oneExp ≠ 0
This closes the power-sum side of §2.2–3 (the R1 chain of StepK7–K16 now needs no
input).  All sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- R1 (paper (2.8)) at every level, unconditionally. -/
theorem R1_all_unc : ∀ d : ℕ, R1Prop F d := by
  exact R1Prop_of_EvalU F (EvalU_all F)

/-- ID2 at every positive level, unconditionally. -/
theorem ID2_all_unc (d : ℕ) (hd : 1 ≤ d) : ID2 F d := by
  exact ID2_of_EvalU F (EvalU_all F) d hd

/-- exponent-one power sums are nonzero at every level, unconditionally. -/
theorem P_oneExp_unc : ∀ d : ℕ, P F d oneExp ≠ 0 := by
  exact P_oneExp_ne_zero_of_EvalU F (EvalU_all F)

end ZagierHoffmanPositiveChar
