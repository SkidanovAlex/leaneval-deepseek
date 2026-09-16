import Submission.ZagierHoffmanProof.StepL54
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L55: MAIN(2)@general-w — the level-2 termination core (SESSION 198, first floor)

The level-2 recursion for A(2)@w (every weight-w tuple expands at level 2) is a
well-founded recursion over weight-w tuples; this module provides its measure and
recursion principle, sorry-free.

DESIGN (SESSION 198; refines SESSION 182b G6(α) and the SESSION 196 ADDENDUM):
  • the only in-domain (1-adm ∧ ¬2-adm) level-2 inputs are the CASE-1 tuples
    (s₂ > q) and the CASE-2 depth-2 (s₁, q) forms.  CASE-2 with s₁ < q terminates
    immediately (case2_level2: all members 2-adm); ¬1-adm inputs terminate via
    H1_expT; so the RECURSION runs only on CASE-1 inputs and their kept members.
  • the Step-1 members of a CASE-1 input s satisfy (prop212_step1 at k = 2, j = 1):
    type-1/type-2: prefix-2 < S := psum s 2 (strict drop);
    type-3: prefix-2 ≤ S, and at = S the member has the front `s₁+1` at position 0
    (type3_sjadd_one_at at j = 1), so its first initial entry is `s₁+1 > s₁`.
  • MEASURE (no Init-lex encoding needed at level 2): l2μ q s := (psum s 2,
    q+1 − headVal q s) in the lexicographic order on ℕ ×ₗ ℕ, where
    headVal q s := the first initial entry (s₁ when s₁ ≤ q, else q+1).  Strict
    prefix drop lowers the first coordinate; = S type-3 members lower the second
    (headVal grows s₁ → s₁+1, so q+1−headVal shrinks).  Hence every Step-1 member
    has lexicographically smaller measure (l2_member_lt), and the recursion
    terminates by the well-foundedness of the lex pair (l2μC_wf via InvImage).

MODULE CONTENT (all F-free): headVal + headVal_le / headVal_pos; the lex-pair
measure l2μ; the two decrease lemmas l2μ_lt_of_psum_lt / l2μ_lt_of_head_lt and the
combined l2_member_lt; the weight-w carrier L2Carrier, the measure on it l2μC, its
well-foundedness l2μC_wf, and ★ l2_induction (the recursion principle: P holds for
all weight-w tuples if each P(s) follows from P on strictly smaller-measure tuples).

LEAN NOTES: the lex pair ℕ ×ₗ ℕ has no Coe from ℕ × ℕ; `<` on it is NOT reducible
by `change` to `Prod.Lex ... (a, b) (c, d)` — the robust way to use it is
`rw [Prod.Lex.lt_iff]` (x < y ↔ (ofLex x).1 < (ofLex y).1 ∨ ...) followed by
`left`/`right` and `change` on the coordinates (ofLex of an ascribed pair is
rfl-transparent); WellFounded via `InvImage.wf f wellFounded_lt`; the recursion
principle transports the carrier induction to the (r, s, hw)-form.

NEXT (SESSION 199): instantiate the level-2 Step-1 inside `l2_induction` — for
in-domain CASE-1 s apply prop212_step1 (k=2, j=1), package the (type-1/type-2/type-3)
members as the AdmExpT Step-1 identity, dispatch each member by 2-adm (admExpT_self)
/ ¬2-adm (recursion, using l2_member_lt for the termination obligation), and splice
with admExpT_combine; CASE-2 via case2_level2; ¬1-adm via H1_expT.  This yields
A(2)@w for every w; then theorem_A(w) for all w via the level-lift (StepL54's
admExp_level_succ) + theoremA_span_eq_of_H + Counting.theorem_A_of_span.  (The j = 0
G5 chains for (q,q) and (q, s₂>q) and the m ≥ 3 β-design remain separate.)
-/

namespace ZagierHoffmanPositiveChar

/-- The first entry of the initial tuple (`q+1` when the first entry exceeds `q`,
i.e. `Init` is empty; `0` only for the empty tuple, which never occurs at weight ≥ 1). -/
noncomputable def headVal (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : ℕ :=
  if pad0 s 0 ≤ q then pad0 s 0 else q + 1

/-- `headVal` never exceeds `q+1`. -/
lemma headVal_le {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) : headVal q s ≤ q + 1 := by
  rw [headVal]
  by_cases h : pad0 s 0 ≤ q
  · rw [if_pos h]
    omega
  · rw [if_neg h]

/-- `headVal` is at least 1 for nonempty tuples. -/
lemma headVal_pos {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) (hr : 0 < r) : 1 ≤ headVal q s := by
  rw [headVal]
  by_cases h : pad0 s 0 ≤ q
  · have hp0 : 0 < pad0 s 0 := by
      have hp0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s hr
      rw [hp0v]
      exact (s ⟨0, by omega⟩).pos
    rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- ★ The level-2 termination measure, as a lexicographic pair (prefix-2, first
initial entry, reversed).  Along the level-2 recursion: members with prefix-2 < S
drop the first coordinate; kept (`= S`) type-3 members raise the first initial entry
from `s₁` to `s₁+1` (front growth at position 0, `j = 1`), lowering the second —
no Init-lex encoding is needed at level 2. -/
noncomputable def l2μ (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : ℕ ×ₗ ℕ :=
  (psum s 2, q + 1 - headVal q s)

/-- ★ Members with strictly smaller prefix-2 have lexicographically smaller measure. -/
lemma l2μ_lt_of_psum_lt {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (hpsum : psum m 2 < psum s 2) : l2μ q m < l2μ q s := by
  rw [Prod.Lex.lt_iff]
  left
  change psum m 2 < psum s 2
  exact hpsum

/-- ★ Members with equal prefix-2 and a strictly larger first initial entry have
lexicographically smaller measure. -/
lemma l2μ_lt_of_head_lt {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (hpsum : psum m 2 = psum s 2) (hhead : headVal q s < headVal q m) :
    l2μ q m < l2μ q s := by
  rw [Prod.Lex.lt_iff]
  right
  constructor
  · change psum m 2 = psum s 2
    exact hpsum
  · change q + 1 - headVal q m < q + 1 - headVal q s
    have hb : headVal q m ≤ q + 1 := headVal_le m
    omega

/-- Combined dispatch: any level-2 Step-1 member `m` of `s` (prefix-2 ≤ S, with
strict drop or first-initial-entry growth when equal) has lexicographically smaller
measure. -/
lemma l2_member_lt {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (h : psum m 2 < psum s 2 ∨ (psum m 2 = psum s 2 ∧ headVal q s < headVal q m)) :
    l2μ q m < l2μ q s := by
  rcases h with hlt | heq
  · exact l2μ_lt_of_psum_lt s m hlt
  · exact l2μ_lt_of_head_lt s m heq.1 heq.2

/-- The carrier of weight-`w` tuples (any depth). -/
abbrev L2Carrier (w : ℕ) := { p : (Σ r : ℕ, Fin r → ℕ+) // weight p.1 p.2 = w }

/-- The measure on the carrier. -/
noncomputable def l2μC (q w : ℕ) (t : L2Carrier w) : ℕ ×ₗ ℕ :=
  l2μ q t.1.2

/-- Well-foundedness of the level-2 dispatch: `l2μ` into the lexicographic pair. -/
lemma l2μC_wf (q w : ℕ) :
    WellFounded (fun a b : L2Carrier w => l2μC q w a < l2μC q w b) := by
  exact InvImage.wf (l2μC q w) wellFounded_lt

/-- ★ The level-2 recursion principle: `P` holds for every weight-`w` tuple if each
step `P(s)` follows from `P` on tuples of strictly smaller measure `l2μ`. -/
theorem l2_induction (q w : ℕ)
    (P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop)
    (hstep : ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      (∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
          l2μ q m < l2μ q s → P r' m hm) → P r s hw) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw := by
  classical
  let Q : L2Carrier w → Prop := fun t => P t.1.1 t.1.2 t.2
  have hfix : ∀ t : L2Carrier w, Q t := by
    exact WellFounded.fix (l2μC_wf q w) (fun t ih => by
      dsimp [Q]
      refine hstep t.1.1 t.1.2 t.2 ?_
      intro r' m hm hlt
      exact ih ⟨⟨r', m⟩, hm⟩ (by dsimp [l2μC]; exact hlt))
  intro r s hw
  exact hfix ⟨⟨r, s⟩, hw⟩

end ZagierHoffmanPositiveChar
