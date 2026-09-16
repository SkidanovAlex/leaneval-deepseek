import Submission.ZagierHoffmanProof.StepL190
import Submission.ZagierHoffmanProof.StepL192
import Submission.ZagierHoffmanProof.StepL151
import Submission.ZagierHoffmanProof.StepL188
import Submission.ZagierHoffmanProof.StepL128

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L193: the theorem-A endgame via the AMBIENT recursion (route (C))

The well-founded recursion that closes the last obligation of theorem_A's span part.
Motive: `Q t := ¬ kAdm t k → AdmExpT F w k t` on the weight-`w` tuples, measure
`ambNu k (Nat.card F) w` (StepL164).  Step at a tuple `s` with `¬ kAdm s k`:

  * `q < s_1` (the head exceeds `q`): the level-1 chain port (StepL192);
  * otherwise `k' := domLevel s` (StepL168) is the tuple's own in-domain level, and
    `kAdm s (k'-1)`, `¬ kAdm s k'`, `k' ≤ k`.  If `k' = 1` the tuple is trapped by
    the `(.,q)`-form at level 1 and StepL188's corner lemma expands it directly;
    for `k' ≥ 2` the ambient dispatch `maink_case_dispatch_amb` (StepL190) runs the
    chains at level `k'` with target `k`, its recursion hypothesis supplied by the
    induction hypothesis (the chains' members descend in `ambNu k` by Steps
    L165/L172/L173/L175).

Consequences: `AkT_all_amb` (every weight-`w` tuple expands at every level), the span
statement `theoremA_span_amb` and the full theorem A `theorem_A_amb` — which is exactly
the statement of `Submission.theorem_A` (`theorem_A_of_mainkT'`, StepL151).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ambient recursion: every weight-`w` tuple that is not `k`-admissible expands at
level `k`, by well-founded recursion on `ambNu k (Nat.card F) w`. -/
theorem maink_amb_all (w : ℕ) (hw0 : 0 < w) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w →
      ¬ kAdmissible (Nat.card F) s k → AdmExpT F w k s := by
  classical
  intro k hk1
  let Q : LkCarrier w → Prop :=
    fun t => ¬ kAdmissible (Nat.card F) t.1.2 k → AdmExpT F w k t.1.2
  have hfix : ∀ t : LkCarrier w, Q t := by
    refine WellFounded.fix
      (InvImage.wf (fun t : LkCarrier w => ambNu k (Nat.card F) w t.1.2) wellFounded_lt) ?_
    intro t ih
    obtain ⟨⟨r, s⟩, hw⟩ := t
    dsimp only [Q]
    intro hnot
    by_cases hbig : (Nat.card F : ℕ) < pad0 s 0
    · -- the head exceeds `q`: the level-1 chain port
      have hr : 0 < r := weight_pos_hr s hw hw0
      have h0 : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
      have hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ) := by rw [← h0]; exact hbig
      refine maink_case1_level1_amb F w hr s hw hgt k hk1 ?_
      intro r' m hm hlt hnotm
      exact ih ⟨⟨r', m⟩, hm⟩ hlt hnotm
    · -- the head is at most `q`
      have hhead : pad0 s 0 ≤ Nat.card F := le_of_not_gt hbig
      have hnall : ¬ AdmEverywhere (Nat.card F) s := fun hall => hnot (hall k)
      by_cases hone : domLevel (Nat.card F) s = 1
      · -- the `domLevel = 1` corner (`(q)` or `Lam`-admissible)
        rcases maink_domLevel_one_of_head_le F w s hw hone hhead k hk1 with h | hadm
        · exact h
        · exact absurd hadm hnot
      · -- the tuple's own in-domain level `k' = domLevel s >= 2`
        have hk'1 : 1 ≤ domLevel (Nat.card F) s := domLevel_pos (Nat.card F) s hnall
        have hk'2 : 2 ≤ domLevel (Nat.card F) s := by
          rcases Nat.lt_or_ge (domLevel (Nat.card F) s) 2 with h | h
          · omega
          · exact h
        have h1' : kAdmissible (Nat.card F) s (domLevel (Nat.card F) s - 1) :=
          kAdmissible_domLevel_pred (Nat.card F) s hnall
        have hnot' : ¬ kAdmissible (Nat.card F) s (domLevel (Nat.card F) s) :=
          not_kAdmissible_domLevel (Nat.card F) s hnall
        have hle : domLevel (Nat.card F) s ≤ k := domLevel_le_of_not_adm (Nat.card F) s hnot
        exact maink_case_dispatch_amb F w (domLevel (Nat.card F) s) r s hw hk'1 hk'2 h1' hnot' k hle
          (fun r' m hm hlt hnotm => ih ⟨⟨r', m⟩, hm⟩ hlt hnotm)
  intro r s hw hnot
  exact hfix ⟨⟨r, s⟩, hw⟩ hnot

/-- The `H_w` tower from the ambient recursion: every weight-`w` tuple expands at every
level `k >= 1`. -/
theorem AkT_all_amb (w : ℕ) (hw0 : 0 < w) (k : ℕ) (hk1 : 1 ≤ k) (r : ℕ) (s : Fin r → ℕ+)
    (hw : weight r s = w) : AdmExpT F w k s := by
  classical
  by_cases h : kAdmissible (Nat.card F) s k
  · exact admExpT_self F w k (weight_pos_hr s hw hw0) s hw h
  · exact maink_amb_all F w hw0 k hk1 r s hw h

/-- theorem-A's span equality at weight `w`. -/
theorem theoremA_span_amb (w : ℕ) (hw : 0 < w) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) :=
  theoremA_span_of_mainkT' F w hw
    (fun k hk1 _ r s hw' _ _ => AkT_all_amb F w hw k hk1 r s hw')

/-- ★★★ THEOREM A (Brown's theorem in positive characteristic) at weight `w`. -/
theorem theorem_A_amb (w : ℕ+) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
      Module.rank (RatFunc F) (𝒵 F w) ≤ d F w :=
  theorem_A_of_mainkT' F w.1 w.pos
    (fun k hk1 _ r s hw' _ _ => AkT_all_amb F w.1 w.pos k hk1 r s hw')

end ZagierHoffmanPositiveChar
