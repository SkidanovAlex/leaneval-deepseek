import Submission.ZagierHoffmanProof.StepL105
import Submission.ZagierHoffmanProof.StepL97
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L106: \u2605 A(2)@w and A(3)@w UNCONDITIONAL (SESSION 253)

\u2605 A2T_all (w) (hw0 : 0 < w) : \u2200 r s hw, AdmExpT F w 2 s \u2014 every
weight-w tuple expands at level 2 in ORDERED form = H_2 at weight w, now
UNCONDITIONAL (A2T_from_main2T + main2T).
\u2605 A3T_all (w) (hw0) : \u2200 r s hw, AdmExpT F w 3 s \u2014 H_3 at weight w,
UNCONDITIONAL (A3_from_main2T + main2T; main3 already closed).
MILESTONE: with H1_expT (StepL51), A2T_all and A3T_all, the whole level \u2264 3
tower at every weight is CLOSED \u2014 the single-ingredient reduction of StepL97 is
fully discharged.  The remaining H_k-tower question is the generic-k main(k) for
k \u2265 4 (PLAN SESSIONS 183d\u2013g), then theorem_A's span assembly at weight w via
A(w)@w + the \ud835\udcb0-membership bridge + Counting.theorem_A_of_span.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ A(2)@w UNCONDITIONALLY: every weight-w tuple expands at level 2 in ORDERED
form (2-adm outputs with prefix orders ℓ ≥ 2) — H_2 at weight w. -/
theorem A2T_all (w : ℕ) (hw0 : 0 < w) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 2 s := by
  exact A2T_from_main2T F w hw0 (main2T F w)

/-- ★ A(3)@w UNCONDITIONALLY: every weight-w tuple expands at level 3 in ORDERED
form (3-adm outputs with prefix orders ℓ ≥ 3) — H_3 at weight w.  With
main3 and main2T closed, the whole level ≤ 3 tower is unconditional. -/
theorem A3T_all (w : ℕ) (hw0 : 0 < w) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 3 s := by
  exact A3_from_main2T F w hw0 (main2T F w)

end ZagierHoffmanPositiveChar
