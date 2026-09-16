import Submission.ZagierHoffmanProof.StepL149
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L150: ★★ `Ak_from_Ak1_maink` — the `A(k)@w` tower step (SESSION 262)
— StepL115 obligation (7)

From the level-`(k−1)` tower statement `Ak1` and the level-`k` IN-DOMAIN handler
`maink : (k−1)-adm → ¬k-adm → AdmExpT F w k`, every weight-`w` tuple expands at
level `k`.

PROOF (direct transcription of StepL96's `A3_from_A2T_and_main3` with
`(2,3) ↦ (k−1,k)`):
  1. `k`-admissible → `admExpT_self` (needs `0 < r` from `weight_pos_hr`);
  2. `(k−1)`-adm ∧ ¬k-adm → `maink`;
  3. `¬(k−1)`-adm → refine the `Ak1` expansion: each output `c i` is `(k−1)`-adm
     (Ak1's `hadm`) and weight `w`; dispatch by k-adm → `admExpT_self` /
     ¬k-adm → `maink` (`hadm` + the negation); the prefix orders transport
     (`k−1 ≤ k`); splice by `admExpT_combine`.
NOTE (the interface decision, SESSION 261 design note): `maink` takes the
`(k−1)`-admissibility — NOT the depth condition `k ≤ r` of StepL115's skeleton and
NOT `Ak1`: `mainkT_in` (the in-domain handler, whose CASE dispatch is StepL149's
`maink_case_dispatch`) is the missing piece, and it is exactly what this step consumes.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ¬`(k−1)`-adm descent: from the level-`(k−1)` tower `Ak1` and the in-domain
handler `maink`, a ¬`(k−1)`-adm weight-`w` tuple expands at level `k`. -/
theorem Ak_not_k1adm (w : ℕ) (k : ℕ) (hk1 : 1 ≤ k)
    {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (Ak1 : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_ : weight r' m = w), AdmExpT F w (k - 1) m)
    (maink : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_ : weight r' m = w),
      kAdmissible (Nat.card F) m (k - 1) → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  rcases Ak1 r s hw with ⟨ι, finι, dep, hdep, c, a, hw', hadm1, horder1, hid⟩
  letI : Fintype ι := finι
  refine admExpT_combine F w k s dep hdep c a hid ?_ ?_
  · intro i ℓ hℓ
    exact horder1 i ℓ (by omega)
  · intro i
    by_cases hki : kAdmissible (Nat.card F) (c i) k
    · exact admExpT_self F w k (hdep i) (c i) (hw' i) hki
    · exact maink (dep i) (c i) (hw' i) (hadm1 i) hki

/-- ★★ The `A(k)@w` tower step: from the level-`(k−1)` tower statement and the
level-`k` in-domain handler, every weight-`w` tuple expands at level `k`. -/
theorem Ak_from_Ak1_maink (w : ℕ) (hw0 : 0 < w) (k : ℕ) (hk1 : 1 ≤ k)
    (Ak1 : ∀ (r : ℕ) (m : Fin r → ℕ+) (_ : weight r m = w), AdmExpT F w (k - 1) m)
    (maink : ∀ (r : ℕ) (s : Fin r → ℕ+) (_ : weight r s = w),
      kAdmissible (Nat.card F) s (k - 1) → ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (_ : weight r s = w), AdmExpT F w k s := by
  classical
  intro r s hw
  by_cases hk : kAdmissible (Nat.card F) s k
  · have hr : 0 < r := weight_pos_hr s hw hw0
    exact admExpT_self F w k hr s hw hk
  · by_cases hk1a : kAdmissible (Nat.card F) s (k - 1)
    · exact maink r s hw hk1a hk
    · exact Ak_not_k1adm F w k hk1 s hw Ak1 maink

end ZagierHoffmanPositiveChar
