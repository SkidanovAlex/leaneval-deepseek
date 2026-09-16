import Submission.ZagierHoffmanProof.StepL104
import Submission.ZagierHoffmanProof.StepL101
import Submission.ZagierHoffmanProof.StepL100
import Submission.ZagierHoffmanProof.StepL56
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L105: \u2605 g5T_total and main2T \u2014 the strengthened G5 total and
MAIN(2)-strengthened UNCONDITIONALLY (SESSION 253)

\u2605 g5T_total (w) : \u2200 r s hw, kAdm1 \u2192 \u00ac kAdm2 \u2192 pad0 s 0 = q
\u2192 AdmExpT F w 2 s \u2014 via l2_induction (P incl. pad0 m 0 = q) with per-step
inDomain2_cases dispatch: CASE-1 (2 \u2264 r \u2227 q < pad0 s 1) \u2192 g5T_case1
(StepL104) with the recursion IH; CASE-2 (r = 2 \u2227 pad0 s 1 = q) \u2192 g5T_case2
(StepL101).
\u2605 main2T (w) : \u2200 r s hw, kAdm1 \u2192 \u00ac kAdm2 \u2192 AdmExpT F w 2 s :=
main2T_of_g5T g5T_total \u2014 MAIN(2)-strengthened is now UNCONDITIONAL.
NEXT: A(2)@w and A(3)@w unconditional at each weight (StepL106):
A2T_from_main2T/A3_from_main2T (StepL97) instantiated with main2T.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ G5T TOTAL (strengthened): every in-domain weight-w tuple with zero-padded
first entry q expands at level 2 in ORDERED form.  CASE-1 (2 ≤ r ∧ q < pad0 s 1)
→ g5T_case1 (recursion on the chain a-members); CASE-2 (r = 2 ∧ pad0 s 1 = q)
→ g5T_case2 ((q,q) leaf). -/
theorem g5T_total (w : ℕ) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 →
      pad0 s 0 = Nat.card F → AdmExpT F w 2 s := by
  classical
  let P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop :=
    fun r s hw => kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 →
      pad0 s 0 = Nat.card F → AdmExpT F w 2 s
  change ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw
  refine l2_induction (Nat.card F) w P ?_
  intro r s hw rec h1 hn2 hq0
  have hcases := inDomain2_cases (Nat.card F) (card_ge_two F) s h1 hn2
  rcases hcases with hc1 | hc2
  · rcases hc1 with ⟨hcase, hbigp⟩
    exact g5T_case1 F w r s hw hcase hbigp hq0
      (fun r' m hm h1m h2m hq0m hdrop => rec r' m hm hdrop h1m h2m hq0m)
  · rcases hc2 with ⟨hr2, hp1⟩
    exact g5T_case2 F w s hw hr2 hp1 hq0

/-- ★ MAIN(2)-strengthened UNCONDITIONALLY: every in-domain (1-adm ∧ ¬2-adm)
weight-w tuple expands at level 2 in ORDERED form. -/
theorem main2T (w : ℕ) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExpT F w 2 s := by
  exact main2T_of_g5T F w (g5T_total F w)

end ZagierHoffmanPositiveChar
