import Submission.ZagierHoffmanProof.StepL95
import Submission.ZagierHoffmanProof.StepL54
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L96: the A(3)@w spine — A3_self / A3_not_two_adm / A3_from_A2T_and_main3 / A3_from_A2T

The strengthened level-3 scaffold (mirror of StepL56's A2_with_main2 at k = 3):
  • A3_self (w s hw hw0 h3) : AdmExpT F w 3 s — a 3-adm weight-w tuple is its own
    level-3 expansion (admExpT_self at k = 3);
  • A3_not_two_adm (w hw0 s hw hn2) (A2T) (main3) : AdmExpT F w 3 s — the
    ¬2-adm descent: A2T (strengthened level-2 at weight w) gives AdmExpT F w 2 s
    with 2-adm weight-w outputs c i (prefix-orders ≥ 2); refine each by
    by_cases 3-adm → admExpT_self / ¬3-adm → main3 (2-adm ∧ ¬3-adm);
    splice by admExpT_combine (orders ≥ 3 inherited from A2T's orders ≥ 2);
  • A3_from_A2T_and_main3 (w hw0) (A2T) (main3) : ∀ r s hw, AdmExpT F w 3 s —
    by_cases 3-adm (self) / 2-adm ∧ ¬3-adm (main3) / ¬2-adm (A3_not_two_adm);
  • A3_from_A2T (w hw0) (A2T) : ∀ r s hw, AdmExpT F w 3 s — main3 is now a
    CLOSED theorem (StepL95), so A(3)@w reduces to the strengthened level-2 handler.
DECOMPOSITION INTO THE H_k TOWER (recorded): for a fixed weight w the tower is
  A(1)@w = H1_expT-restricted (closed, weight-uniform, StepL51);
  A(k)@w = A(k−1)@w + main(k)@w, 2 ≤ k ≤ w, where main(k)@w is the in-domain
  (k−1)-adm ∧ ¬k-adm handler at level k and the descent case ¬(k−1)-adm uses
  A(k−1)@w (refine each (k−1)-adm output by k-adm self / main(k)) — the A3_not_*
  shape above is this generic descent at k = 3.
  Currently open tower ingredients: (i) A(2)@w (strengthened; the committed level-2
  results A2_weak_all/MAIN2_weak_all are the WEAK AdmExp form WITHOUT prefix orders
  — main2's strengthened splices + A2T remain to close); (ii) main(k)@w for k ≥ 4
  (the generic-k MAIN(k) of PLAN SESSIONS 183d–g).  main3@w (k=3) is CLOSED.
theorem_A's span then uses A(w)@w (outputs w-adm = workspace-admissible) + the
𝒰-membership bridge + Counting.theorem_A_of_span.  theorem_B/D remain
ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A 3-admissible weight-w tuple is its own level-3 expansion. -/
theorem A3_self (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hw0 : 0 < w) (h3 : kAdmissible (Nat.card F) s 3) : AdmExpT F w 3 s := by
  classical
  have hr : 0 < r := weight_pos_hr s hw hw0
  exact admExpT_self F w 3 hr s hw h3

/-- ¬2-adm level-3 descent: from the strengthened level-2 expansion A2T + the
in-domain handler main3, every weight-w tuple expands at level 3 (refine each 2-adm
A2T-output by 3-adm self / main3). -/
theorem A3_not_two_adm (w : ℕ) (hw0 : 0 < w) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hn2 : ¬ kAdmissible (Nat.card F) s 2)
    (A2T : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w), AdmExpT F w 2 m)
    (main3 : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 2 → ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    AdmExpT F w 3 s := by
  classical
  have hA2 := A2T r s hw
  rcases hA2 with ⟨ι, finι, dep, hdep, c, a, hw', hadm2, horder2, hid⟩
  letI : Fintype ι := finι
  refine admExpT_combine F w 3 s dep hdep c a hid ?_ ?_
  · intro i ℓ hℓ
    exact horder2 i ℓ (by omega : 2 ≤ ℓ)
  · intro i
    by_cases h3i : kAdmissible (Nat.card F) (c i) 3
    · have hdi : 0 < dep i := hdep i
      exact admExpT_self F w 3 hdi (c i) (hw' i) h3i
    · exact main3 (dep i) (c i) (hw' i) (hadm2 i) h3i

/-- A(3)@w spine from the strengthened level-2 handler: given A2T (every weight-w
tuple is AdmExpT F w 2) and the (now unconditional) in-domain level-3 handler main3,
every weight-w tuple is AdmExpT F w 3. -/
theorem A3_from_A2T_and_main3 (w : ℕ) (hw0 : 0 < w)
    (A2T : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w), AdmExpT F w 2 m)
    (main3 : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 2 → ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 3 s := by
  classical
  intro r s hw
  by_cases h3 : kAdmissible (Nat.card F) s 3
  · have hr : 0 < r := weight_pos_hr s hw hw0
    exact admExpT_self F w 3 hr s hw h3
  · by_cases h2 : kAdmissible (Nat.card F) s 2
    · exact main3 r s hw h2 h3
    · exact A3_not_two_adm F w hw0 s hw h2 A2T main3

/-- A(3)@w unconditionally modulo the strengthened level-2 handler: main3 is now a
closed theorem, so A3@w reduces to A2T. -/
theorem A3_from_A2T (w : ℕ) (hw0 : 0 < w)
    (A2T : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w), AdmExpT F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 3 s := by
  exact A3_from_A2T_and_main3 F w hw0 A2T
    (fun r' m hm h2m h3m => main3 F w hw0 r' m hm h2m h3m)

end ZagierHoffmanPositiveChar
