import Submission.ZagierHoffmanProof.StepL127
import Submission.ZagierHoffmanProof.StepL107
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L128: the μ3 measure and the relation `MainkStep3` (β) (SESSION 258u)

The paper's Prop-3.2 continuation measure (PLAN SESSION 258q) as a three-coordinate
lex product:
    μ3(s) = ( psum s k ,  (q+2)^(w+1) − 1 − initVal q w s ,  pad0 s (initLen q s) )
and the recursion relation
    MainkStep3 k q w s m  ⟺  C1 ∨ C2′ ∨ C3
      C1 : psum m k < psum s k                              (strict prefix-k drop)
      C2′: psum m k = psum s k ∧ initVal q w s < initVal q w m   (Init strictly grows)
      C3 : psum m k = psum s k ∧ initVal q w m = initVal q w s ∧
           pad0 m (initLen q m) < pad0 s (initLen q s)        (entry at Init-length drops)
Well-foundedness: Subrelation.wf + InvImage.wf of μ3 (the three decrease lemmas
below; C2′/C3 supplied by StepL127's init-bound for the mixed type-1 members).
The existing `MainkStep` (C1 ∨ equal-prefix + InitLt) embeds into `MainkStep3`
via `initVal_lex_lt` — so all existing lk-induction uses remain valid, while the
mixed type-1 members (≤ prefix-k at the output level, initiating growth) become
dispatchable.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The μ3 measure at level `k`: prefix-k sum, reversed initial value, entry at
the Init length (lex, leftmost most significant). -/
noncomputable def lkμ3 (k q w : ℕ) (t : LkCarrier w) : (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  toLex (toLex (psum t.1.2 k, (q + 2) ^ (w + 1) - 1 - initVal q w t.1.2),
    pad0 t.1.2 (initLen q t.1.2))

/-- C1: a strict prefix-k drop decreases μ3 (first coordinate). -/
lemma lkμ3_lt_of_psum_lt (k q w : ℕ) {t u : LkCarrier w}
    (h : psum u.1.2 k < psum t.1.2 k) : lkμ3 k q w u < lkμ3 k q w t := by
  rw [Prod.Lex.lt_iff]
  left
  rw [Prod.Lex.lt_iff]
  left
  simpa [lkμ3] using h

/-- C2′: at equal prefix-k, strict Init-growth decreases μ3 (second coordinate). -/
lemma lkμ3_lt_of_initVal (k q w : ℕ) {t u : LkCarrier w}
    (heq : psum u.1.2 k = psum t.1.2 k) (hiv : initVal q w t.1.2 < initVal q w u.1.2) :
    lkμ3 k q w u < lkμ3 k q w t := by
  rw [Prod.Lex.lt_iff]
  left
  rw [Prod.Lex.lt_iff]
  right
  constructor
  · simpa [lkμ3] using heq
  · have hMu : initVal q w u.1.2 < (q + 2) ^ (w + 1) := initVal_lt_pow q w u.1.2 u.2
    have hivM1 : initVal q w t.1.2 < (q + 2) ^ (w + 1) - 1 := by
      have hle : initVal q w u.1.2 ≤ (q + 2) ^ (w + 1) - 1 := Nat.le_sub_one_of_lt hMu
      omega
    simpa [lkμ3] using Nat.sub_lt_sub_left hivM1 hiv

/-- C3: at equal prefix-k and equal Init-value, a strict drop of the entry at
the Init length decreases μ3 (third coordinate). -/
lemma lkμ3_lt_of_entry (k q w : ℕ) {t u : LkCarrier w}
    (heq : psum u.1.2 k = psum t.1.2 k) (hiv : initVal q w u.1.2 = initVal q w t.1.2)
    (hdrop : pad0 u.1.2 (initLen q u.1.2) < pad0 t.1.2 (initLen q t.1.2)) :
    lkμ3 k q w u < lkμ3 k q w t := by
  rw [Prod.Lex.lt_iff]
  right
  constructor
  · have hiv' : (q + 2) ^ (w + 1) - 1 - initVal q w u.1.2
        = (q + 2) ^ (w + 1) - 1 - initVal q w t.1.2 := by rw [hiv]
    show toLex (psum u.1.2 k, (q + 2) ^ (w + 1) - 1 - initVal q w u.1.2)
        = toLex (psum t.1.2 k, (q + 2) ^ (w + 1) - 1 - initVal q w t.1.2)
    rw [heq, hiv']
  · simpa [lkμ3] using hdrop

/-- The (β)-recursion relation at level `k` (C1 ∨ C2′ ∨ C3). -/
def MainkStep3 (k q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+) : Prop :=
  psum m k < psum s k
  ∨ (psum m k = psum s k ∧ initVal q w s < initVal q w m)
  ∨ (psum m k = psum s k ∧ initVal q w m = initVal q w s ∧
     pad0 m (initLen q m) < pad0 s (initLen q s))

/-- ★ Well-foundedness of the (β)-relation: μ3 is a strictly decreasing measure. -/
theorem maink_step3_wf (k q w : ℕ) :
    WellFounded (fun m s : LkCarrier w => MainkStep3 k q w s.1.2 m.1.2) := by
  refine Subrelation.wf ?_ (InvImage.wf (lkμ3 k q w) wellFounded_lt)
  intro m s h
  rcases h with hlt | ⟨heq, hiv⟩ | ⟨heq, hiv, hdrop⟩
  · exact lkμ3_lt_of_psum_lt k q w hlt
  · exact lkμ3_lt_of_initVal k q w heq hiv
  · exact lkμ3_lt_of_entry k q w heq hiv hdrop

/-- The old `MainkStep` embeds into `MainkStep3` (the InitLt case gives strict
`initVal` growth via `initVal_lex_lt`), so all existing lk-induction uses remain
valid under the refined relation. -/
lemma maink_step_to_step3 (k q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (hs : weight r s = w) (hm : weight r' m = w) (h : MainkStep k q s m) :
    MainkStep3 k q w s m := by
  rcases h with hlt | ⟨heq, hlex⟩
  · exact Or.inl hlt
  · refine Or.inr (Or.inl ⟨heq, ?_⟩)
    exact initVal_lex_lt q w s hs m hm hlex

end ZagierHoffmanPositiveChar
