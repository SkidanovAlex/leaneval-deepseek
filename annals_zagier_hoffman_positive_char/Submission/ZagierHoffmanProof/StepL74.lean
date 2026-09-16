import Submission.ZagierHoffmanProof.StepL73
import Submission.ZagierHoffmanProof.StepL60
/-!
# Step L74: MAIN(2)-weak and A(2)-weak from the j = 0 G5 hypothesis (SESSION 225)

With the CASE-1 j = 1 splice (StepL73) closed, the level-2 in-domain handler
MAIN(2)-weak and the full H_2 = A(2)-weak are assembled modulo the two top-level
j = 0 (G5) chain instances:
  ★ MAIN2_weak_of_g5 (w) (g5) : ∀ in-domain weight-w s, AdmExp F w 2 s
      — l2_induction (StepL55) with P(r s hw) := 1-adm → ¬2-adm → AdmExp F w 2 s;
      per step inDomain2_cases (StepL56): CASE-1 (2 ≤ r ∧ q < pad0 s 1): s₁ < q →
      main2_case1_j1 (StepL73, recursion IH = l2_induction's rec at the member
      measure drop), s₁ = q → g5 (the (q, s₂>q) form); CASE-2 (r = 2 ∧ pad0 s 1 =
      q): s₁ < q → main2_case2 (StepL60, closed), s₁ = q → g5 (the (q,q) form).
      The s₁ = q detector is s1_eq_of_not_lt (StepL60).  G5 is TOP-LEVEL only:
      recursion members of j=0-form are dispatched by the IH (SESSION 203).
  ★ A2_not_one_adm_weak / A2_with_main2_weak — weak-AdmExp mirrors of StepL56's
      AdmExpT versions (H1_exp weak (StepL37) + admExp_self + admExp_combine, no
      prefix orders).
  ★ A2_weak_of_g5 (w) (hw0) (g5) : ∀ weight-w s, AdmExp F w 2 s — H_2 at weight w
      from the G5 hypothesis.  G5's exact signature is now pinned:
        g5 : ∀ r m (hm : weight r m = w), 1-adm m → ¬2-adm m → pad0 m 0 = q →
             AdmExp F w 2 m
      (only the depth-2 (q,q) and (q, s₂>q) tuples satisfy these).
NEXT: prove the G5 chains themselves (the j = 0 instances of Prop 2.12/2.13's chain:
empty front, no B*, BCqIter (k−j−1) = 1 over the tail relation / r1Rel — the paper's
s_0 := 0 convention; see PLAN SESSION 225 G5 ANALYSIS), instantiate, and obtain
MAIN2-weak / A2-weak unconditionally.  Named gates unchanged: m≥3 hierarchy (β),
theorem_B/D.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ¬1-adm weak LEM: from H1 (weak level-1 expansion) + per-output self/in-domain
dispatch, a ¬1-adm weight-w tuple expands at level 2. -/
theorem A2_not_one_adm_weak (w : ℕ) (hw0 : 0 < w) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hn1 : ¬ kAdmissible (Nat.card F) s 1)
    (inDom : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExp F w 2 m) :
    AdmExp F w 2 s := by
  classical
  have hr : 0 < r := weight_pos_hr s hw hw0
  have hA1 : AdmExp F w 1 s := by
    have h1 := H1_exp F r hr s
    simpa [hw] using h1
  rcases hA1 with ⟨ι, finι, dep, hdep, c, a, hw', hadm', hid⟩
  letI : Fintype ι := finι
  refine admExp_combine F w 2 s dep hdep c a hid ?_
  intro i
  by_cases h2i : kAdmissible (Nat.card F) (c i) 2
  · have hdi : 0 < dep i := hdep i
    exact admExp_self F w 2 hdi (c i) (hw' i) h2i
  · exact inDom (dep i) (c i) (hw' i) (hadm' i) h2i

/-- Weak A(2)-scaffold: every weight-w tuple expands at level 2 given the in-domain
handler `main2` (weak AdmExp level, no prefix orders). -/
theorem A2_with_main2_weak (w : ℕ) (hw0 : 0 < w)
    (main2 : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExp F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExp F w 2 s := by
  intro r s hw
  by_cases h2 : kAdmissible (Nat.card F) s 2
  · have hr : 0 < r := weight_pos_hr s hw hw0
    exact admExp_self F w 2 hr s hw h2
  · by_cases h1 : kAdmissible (Nat.card F) s 1
    · exact main2 r s hw h1 h2
    · exact A2_not_one_adm_weak F w hw0 s hw h1 main2

/-- ★ MAIN(2)-weak from the j = 0 G5 hypothesis: the in-domain (1-adm ∧ ¬2-adm)
handler.  The l2_induction step dispatches inDomain2_cases: CASE-1 s₂ > q: j = 1
(s₁ < q, main2_case1_j1 with the recursion IH on the members) or j = 0 (s₁ = q, the
G5 (q, s₂>q) hypothesis); CASE-2 (r=2, s₂=q): s₁ < q (main2_case2, no recursion) or
s₁ = q (the G5 (q,q) hypothesis).  Members of the recursion are never j=0-forms
(SESSION 203 finding (1)) — G5 is top-level-only. -/
theorem MAIN2_weak_of_g5 (w : ℕ)
    (g5 : ∀ (r : ℕ) (m : Fin r → ℕ+) (hm : weight r m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      pad0 m 0 = Nat.card F → AdmExp F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExp F w 2 s := by
  classical
  let P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop :=
    fun r s hw => kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExp F w 2 s
  change ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw
  refine l2_induction (Nat.card F) w P ?_
  intro r s hw rec h1 hn2
  have hcases := inDomain2_cases (Nat.card F) (card_ge_two F) s h1 hn2
  rcases hcases with hc1 | hc2
  · rcases hc1 with ⟨hcase, hbigp⟩
    by_cases hs1 : pad0 s 0 < Nat.card F
    · exact main2_case1_j1 F w s hw h1 hn2 hcase hbigp hs1
        (fun r' m hm h1m h2m hμ => rec r' m hm hμ h1m h2m)
    · have hs0 : pad0 s 0 = Nat.card F := s1_eq_of_not_lt (Nat.card F) s h1 hs1
      exact g5 r s hw h1 hn2 hs0
  · rcases hc2 with ⟨hr2, hp1⟩
    by_cases hs1 : pad0 s 0 < Nat.card F
    · exact main2_case2 F w s hw hr2 hp1 hs1
    · have hs0 : pad0 s 0 = Nat.card F := s1_eq_of_not_lt (Nat.card F) s h1 hs1
      exact g5 r s hw h1 hn2 hs0

/-- ★ A(2)-weak from the j = 0 G5 hypothesis: every weight-w tuple expands at level
2 (2-adm outputs) — H_2 at weight w, modulo G5's two j = 0 chain instances. -/
theorem A2_weak_of_g5 (w : ℕ) (hw0 : 0 < w)
    (g5 : ∀ (r : ℕ) (m : Fin r → ℕ+) (hm : weight r m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      pad0 m 0 = Nat.card F → AdmExp F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExp F w 2 s := by
  classical
  exact A2_with_main2_weak F w hw0 (MAIN2_weak_of_g5 F w g5)
end ZagierHoffmanPositiveChar
