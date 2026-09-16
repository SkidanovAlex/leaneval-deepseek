import Submission.ZagierHoffmanProof.StepL178
import Submission.ZagierHoffmanProof.StepL151

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L179: THE TIE CASE — the closure lemma, the invariant-carrying tower and the
# `AdmExpTie` endgame reduction (architecture (A′) of PLAN SESSION 271)

The residual of the theorem_A span endgame (PLAN SESSION 271, all four formulations) is the
TIE CASE: a member `m` of a level-`k` chain that ties with the input `x` at level `k`
(`psum m k = psum x k`, hence `MainkStep3` gives C2′/C3) and whose level-`(k−1)` tower output
`c` also ties at level `k` (`psum c k = psum m k`).  This module
  • ★★ `lkμ3_lt_of_tie_member` — CLOSES the tie case as soon as the tower supplies the
    `Init`-transference data (`initVal m ≤ initVal c`, plus the C3 entry comparison): the C2′
    branch chains `initVal x < initVal m ≤ initVal c`, the C3 branch chains the entry drops, and
    `lkμ3_lt_of_psum_le_and_init` (StepL176) turns either into the strict μ3 drop that the
    well-founded recursion needs.  This is the exact remaining obligation of the recursion,
    named and localised;
  • ★★ `AkT_all_of_mainkTie` — the `H_w` tower for the invariant-carrying expansions
    (`AdmExpTie w k Λ`, tie level `Λ`), by induction on the level via StepL177's
    `Ak_from_Ak1_maink_tie`;
  • ★★★ `theoremA_span_of_mainkTie` / `theorem_A_of_mainkTie` — the ENDGAME: the span equality
    (and the rank bound) of theorem_A follow from the level-1 invariant base plus the
    invariant-carrying in-domain handler at every level `k ≥ 2` (the invariant is forgotten at
    the last step).
⇒ After this module the whole span path is: (1) the level-1 invariant base `A1Tie`,
  (2) the invariant-carrying in-domain handler `mainkTie` at every level, whose ONLY non-local
  input is the `Init`-transference data of `lkμ3_lt_of_tie_member` for the chains' tie members.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ THE TIE-CASE CLOSURE.  Let `m` be a chain member tying with the input `x` at level `k`
(`MainkStep3 k q w x m`, `psum m k = psum x k`) and `c` a tie output of its level-`(k−1)`
refinement (`psum c k ≤ psum x k`).  If the tower supplies the `Init`-transference
`initVal m ≤ initVal c` (and, in the equal case, the entry comparison of `c` and `m`), then `c`
is STRICTLY below `x` in the μ3-at-`k` measure — exactly the decrease the well-founded
recursion of `maink` needs for the residual case. -/
theorem lkμ3_lt_of_tie_member (k q w : ℕ) {rx rm rc : ℕ}
    (x : Fin rx → ℕ+) (m : Fin rm → ℕ+) (c : Fin rc → ℕ+)
    (hxw : weight rx x = w) (hcw : weight rc c = w)
    (htie : psum m k = psum x k)
    (hstep : MainkStep3 k q w x m)
    (hmc : initVal q w m ≤ initVal q w c)
    (hentry : initVal q w m = initVal q w c →
      pad0 c (initLen q c) ≤ pad0 m (initLen q m))
    (hcs : psum c k ≤ psum x k) :
    lkμ3 k q w ⟨⟨rc, c⟩, hcw⟩ < lkμ3 k q w ⟨⟨rx, x⟩, hxw⟩ := by
  have hdata : initVal q w x < initVal q w c ∨
      (initVal q w x = initVal q w c ∧
        pad0 c (initLen q c) < pad0 x (initLen q x)) := by
    rcases hstep with hlt | ⟨heq, hiv⟩ | ⟨heq, hiv, hdrop⟩
    · rw [htie] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact Or.inl (lt_of_lt_of_le hiv hmc)
    · rcases lt_or_eq_of_le hmc with hlt | heq2
      · exact Or.inl (by rw [← hiv]; exact hlt)
      · refine Or.inr ⟨by rw [← hiv]; exact heq2, ?_⟩
        exact lt_of_le_of_lt (hentry heq2) hdrop
  exact lkμ3_lt_of_psum_le_and_init k q w x c hxw hcw hcs hdata

/-- ★★ The `H_w` TOWER carrying the `AdmExpTie` invariant at the tie level `Λ`: from the
level-1 invariant base and the invariant-carrying in-domain handler, every weight-`w` tuple has
a `j`-level tie-invariant expansion for every `1 ≤ j ≤ Λ`. -/
theorem AkT_all_of_mainkTie (w : ℕ) (hw : 0 < w) (Λ : ℕ)
    (A1Tie : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTie F w 1 Λ s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpTie F w k Λ s) :
    ∀ (k : ℕ) (_ : 1 ≤ k) (_ : k ≤ Λ), ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w →
      AdmExpTie F w k Λ s := by
  classical
  intro k
  induction k with
  | zero => intro hk1 _; omega
  | succ k ih =>
      intro hk1 hkΛ r s hw'
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using A1Tie r s hw'
      · exact Ak_from_Ak1_maink_tie F w hw Λ (k + 1) (by omega) (by omega)
          (fun r' m hm => ih (by omega) (by omega) r' m hm)
          (maink (k + 1) (by omega) (by omega)) r s hw'

/-- ★★★ theorem-A's span equality from the level-1 invariant base and the invariant-carrying
in-domain handler (tie level `w`). -/
theorem theoremA_span_of_mainkTie (w : ℕ) (hw : 0 < w)
    (A1Tie : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTie F w 1 w s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpTie F w k w s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) := by
  classical
  refine theoremA_span_eq_of_H F w hw ?_
  intro r s hw'
  have h1 : AdmExpTie F w w w s :=
    AkT_all_of_mainkTie F w hw w A1Tie maink w (by omega) (le_refl w) r s hw'
  exact admExpT_to_AdmExp F w w s (admExpTie_to_admExpT F w w w s h1)

/-- ★★★ theorem-A (span equality + rank bound) from the invariant-carrying handler. -/
theorem theorem_A_of_mainkTie (w : ℕ) (hw : 0 < w)
    (A1Tie : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTie F w 1 w s)
    (maink : ∀ (k : ℕ) (_ : 1 ≤ k) (_ : 2 ≤ k) (r : ℕ) (s : Fin r → ℕ+),
      weight r s = w → kAdmissible (Nat.card F) s (k - 1) →
        ¬ kAdmissible (Nat.card F) s k → AdmExpTie F w k w s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
      Module.rank (RatFunc F) (𝒵 F w) ≤ d F w :=
  theorem_A_of_span F ⟨w, hw⟩ (theoremA_span_of_mainkTie F w hw A1Tie maink)

end ZagierHoffmanPositiveChar
