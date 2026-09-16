import Submission.ZagierHoffmanProof.StepL96
import Submission.ZagierHoffmanProof.StepL56
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L97: tower state — main2T ⇒ A(1,2,3)@w (SESSION 250)

The H_k tower at a fixed weight w, reduced to its open ingredients:
  A(1)@w  closed (H1_expT, weight-uniform, StepL51);
  A(2)@w  = A2T_from_main2T (main2T)  — A2_with_main2 (StepL56), closed modulo the
    strengthened in-domain level-2 handler main2T;
  A(3)@w  = A3_from_main2T (main2T)   — A3_from_A2T (StepL96) + A2T_from_main2T;
    main3 (StepL95) is CLOSED, so the k=3 in-domain side is unconditional.
So for levels k ≤ 3 the ONLY open ingredient is
  main2T (w) (hw0) : ∀ r s hw, kAdm q s 1 → ¬ kAdm q s 2 → AdmExpT F w 2 s
(the strengthened level-2 in-domain handler).  The committed level-2 machinery is
WEAK (AdmExp: MAIN2_weak_all/g5_total/main2_case1_j1 … lack prefix orders); the
CASE-2 leaf (A2_case2/case2_level2) is already AdmExpT.  main2T therefore needs the
strengthened port of the level-2 CASE-1 j=1 splice (main2_case1_j1 at the AdmExpT
level — mirror main3_case1_j1/88/89's strengthened script at (k=2, j=1) with the
generic-k prop212/type* machinery) plus the strengthened G5 (q,·)/(q,q) chains.
NEXT (recorded): close main2T (the strengthened level-2 port), then A(3)@w is
unconditional via A3_from_main2T; afterwards the generic-k tower for k ≥ 4.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A(2)@w = A2T from main2T: A2_with_main2 (StepL56) wrapped in the ∀-form. -/
theorem A2T_from_main2T (w : ℕ) (hw0 : 0 < w)
    (main2T : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExpT F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 2 s := by
  exact A2_with_main2 F w hw0 main2T

/-- A(3)@w from main2T: A3_from_A2T (StepL96) + A2T_from_main2T — with main3 CLOSED,
the whole level ≤ 3 tower reduces to the strengthened level-2 handler. -/
theorem A3_from_main2T (w : ℕ) (hw0 : 0 < w)
    (main2T : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExpT F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 3 s := by
  exact A3_from_A2T F w hw0 (A2T_from_main2T F w hw0 main2T)

end ZagierHoffmanPositiveChar
