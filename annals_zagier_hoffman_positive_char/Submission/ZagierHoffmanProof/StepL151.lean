import Submission.ZagierHoffmanProof.StepL150
import Submission.ZagierHoffmanProof.StepL36
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L151: ★★★ the `H_w` TOWER and theorem-A's span endgame from `mainkT_in`
(SESSION 262)

The whole remaining endgame of theorem_A's span part, packaged once the level-`k`
IN-DOMAIN handler `maink` (= `mainkT_in`, whose CASE body is StepL149's
`maink_case_dispatch`) and the level-1 base `A1T` are available:
  • ★★ `AkT_all_of_mainkT` — the tower: by induction on `k`, `A(1)@w` from `A1T` and
    `A(k+1)@w` from `A(k)@w` by StepL150's `Ak_from_Ak1_maink`; hence `A(k)@w` for
    EVERY `k ≥ 1`;
  • ★★★ `theoremA_span_of_mainkT` — `𝒵 F w = span K (𝒯 F w)` at weight w
    (`theoremA_span_eq_of_H` (StepL36) + `admExpT_to_AdmExp` (StepL49) at `k = w`);
  • ★★★ `theorem_A_of_mainkT` — the full theorem-A conclusion at weight w
    (`Counting.theorem_A_of_span`, i.e. the span equality AND the rank bound).
WHAT REMAINS (SESSION 261 design note): `mainkT_in` itself — the well-founded
recursion over `MainkStep3 k q w` whose predicate/hypothesis bookkeeping is the only
gap (the CASE dispatch and both remaining sub-lemmas are DONE/comitted).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ The `H_w` tower: from the level-1 base and the in-domain handler `maink`,
every weight-`w` tuple expands at EVERY level `k ≥ 1`. -/
theorem AkT_all_of_mainkT (w : ℕ) (hw : 0 < w)
    (A1T : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpT F w 1 s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    ∀ (k : ℕ) (_ : 1 ≤ k), ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w →
      AdmExpT F w k s := by
  classical
  intro k
  induction k with
  | zero => intro hk1; omega
  | succ k ih =>
      intro hk1 r s hw'
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using A1T r s hw'
      · exact Ak_from_Ak1_maink F w hw (k + 1) (by omega)
          (fun r' m hm => ih (by omega : 1 ≤ k) r' m hm)
          (maink (k + 1) (by omega) (by omega)) r s hw'

/-- ★ The level-1 base `A(1)@w` at weight `w`: every weight-`w` tuple expands at
level 1 (StepL51's unconditional `H1_expT`). -/
theorem A1T_all (w : ℕ) (hw : 0 < w) :
    ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpT F w 1 s := by
  intro r s hw'
  have hr : 0 < r := weight_pos_hr s hw' hw
  have h := H1_expT F r hr s
  rwa [hw'] at h

/-- ★★★ theorem-A's span equality at weight `w`, from the tower. -/
theorem theoremA_span_of_mainkT (w : ℕ) (hw : 0 < w)
    (A1T : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpT F w 1 s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) := by
  classical
  refine theoremA_span_eq_of_H F w hw ?_
  intro r s hw'
  exact admExpT_to_AdmExp F w w s
    (AkT_all_of_mainkT F w hw A1T maink w (by omega) r s hw')

/-- ★★★ theorem-A at weight `w` (span equality + rank bound), from the tower. -/
theorem theorem_A_of_mainkT (w : ℕ) (hw : 0 < w)
    (A1T : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpT F w 1 s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
      Module.rank (RatFunc F) (𝒵 F w) ≤ d F w := by
  exact theorem_A_of_span F ⟨w, hw⟩ (theoremA_span_of_mainkT F w hw A1T maink)

/-- ★★★ theorem-A's span equality at weight `w` from the IN-DOMAIN handler ALONE
(the level-1 base is `H1_expT`). -/
theorem theoremA_span_of_mainkT' (w : ℕ) (hw : 0 < w)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) :=
  theoremA_span_of_mainkT F w hw (A1T_all F w hw) maink

/-- ★★★ theorem-A at weight `w` (span + rank) from the IN-DOMAIN handler ALONE. -/
theorem theorem_A_of_mainkT' (w : ℕ) (hw : 0 < w)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
      Module.rank (RatFunc F) (𝒵 F w) ≤ d F w :=
  theorem_A_of_mainkT F w hw (A1T_all F w hw) maink

end ZagierHoffmanPositiveChar
