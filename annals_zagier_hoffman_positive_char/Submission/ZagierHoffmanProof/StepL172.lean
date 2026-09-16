import Submission.ZagierHoffmanProof.StepL171
import Submission.ZagierHoffmanProof.StepL165

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L172: ★★ the G5 a-side AMBIENT STEP

The G5 (all-`q` front) chain of `maink_case1_j0` (StepL146) applied at its own level `k`
with AMBIENT target `Λ ≥ k` needs, for every a-member `D.cA i`, the measure descent
`ambNu Λ m < ambNu Λ s` (the `(C1) ∨ (C2') ∨ (C3)` cases of the ambient measure).
This module assembles it from
  • `maink_g5_aSide_order` (StepL145): `psum m ℓ ≤ psum s ℓ` for `ℓ ≥ k` (ambient horder),
  • `maink_g5_aSide_weight` (StepL140): `weight (D.depA i) (D.cA i) = weight r s`,
  • `maink_g5_aSide_dep_ge` (StepL170): `r ≤ D.depA i`  (depth invariant),
  • `maink_g5_aSide_Init` (StepL171): the `Init` tie-break,
exactly along StepL165's `type1_amb_step`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ The G5 a-side ambient step: every a-member decreases `ambNu Λ` from `s`. -/
theorem maink_g5_aSide_amb_step (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      ∀ (w : ℕ), weight r s = w → ∀ (Λ : ℕ), k ≤ Λ →
        ambNu Λ (Nat.card F) w (D.cA i) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D i hi w hw Λ hΛ
  have hle := maink_g5_aSide_order F r s k hk1 hkr hbig hallq R0 u hpref i hi Λ hΛ
  have hdep := maink_g5_aSide_dep_ge F r s k hk1 hkr hbig R0 u hwtA hpref i hi
  have hmw : weight (D.depA i) (D.cA i) = w :=
    (maink_g5_aSide_weight F r s k hk1 hkr hallq R0 u hwtA i hi).trans hw
  have hmd_le : D.depA i ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : r ≤ w := by
    rw [← hw]
    exact weight_ge_depth r s
  rcases lt_or_eq_of_le hdep with hlt | heq
  · exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle
  · have hInit := maink_g5_aSide_Init F r s k hk1 hkr hbig hallq R0 u hhead i hi
    rcases lt_or_eq_of_le hle with hplt | hpeq
    · exact ambNu_lt_of_psum_lt Λ (Nat.card F) w s _ hplt
    · rcases hInit with hlex | ⟨heqi, hdrop⟩
      · have hiv := initVal_lex_lt (Nat.card F) w s hw (D.cA i) hmw hlex
        exact ambNu_lt_of_initVal Λ (Nat.card F) w s _ hw hmw hpeq heq hiv
      · have hval_eq : initVal (Nat.card F) w (D.cA i) = initVal (Nat.card F) w s := by
          rw [initVal, initVal, heqi]
        exact ambNu_lt_of_entry Λ (Nat.card F) w s _ hpeq heq hval_eq hdrop

end ZagierHoffmanPositiveChar
