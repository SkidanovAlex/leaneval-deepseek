import Submission.ZagierHoffmanProof.StepL106
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L107: the generic level-k recursion infrastructure (SESSION 254)

The foundation of main(k) for every k (the H_k tower's level-k in-domain handler):
  • MainkStep (k q) s m := psum m k < psum s k ∨ (psum m k = psum s k ∧ InitLt q s m);
  • mk_member_step (k q) s m : psum-k < ∨ (≤ ∧ InitLt) → MainkStep (the
      l3_member_step generalization);
  • LkCarrier w / lkμ (k q w) (the (psum-k, M−1−initVal) lex measure, generic k);
  • ★ maink_step_wf (k q w) : WellFounded (MainkStep k q) on weight-w tuples;
  • ★ lk_induction (k q w) (hwf) P hstep : the level-k recursion principle
      (P holds ∀ weight-w tuples if each step follows from P on dispatch-calls);
  • ★ levelk_inDomain_cases (k q hq hk1 s hkminus1 hnot) : a (k−1)-adm ∧
      ¬k-adm tuple is (k ≤ r ∧ q < pad0 s (k−1)) [CASE-1: k-th entry > q] or
      (r = k ∧ first k−1 ≤ q ∧ pad0 s (k−1) = q) [CASE-2: depth-k, last = q].
      (KEY observation recorded: with (k−1)-adm ∧ ¬k-adm, the only possible
      bad entry among the first k positions is the k-th — so CASE-1 has NO j-split
      beyond j = k−1 vs the (k−2)-prefix-q patterns; CASE-1 subcases by the
      (k−1)-st entry < q (the (k, k−1) prop212 chain) or = q (the all-q
      (k−1)-front G5-style chains).)
RESISTING CONJUNCTS of main(k) (recorded for the splices): the level-k member
(k−1)-adm facts (the level3_j*_twoAdm / q_type*_T_of analogues at level k, k-symbolic)
and the member prefix-k order lemmas (the type*_psum_ge_k_le at (k, ·) with the
(k−1)-front arithmetic).  The generic (k,j) machinery (zeta_214_reindexed,
prop212/prop213_step1, type* weight/drop/order lemmas, StepL107's recursion) is the
substrate; the splices are k-symbolic ports of StepL99/L104's scripts.
NEXT: main(k)'s CASE-1 (k, k−1)-splice (the generic port of main2T_case1_j1/
main3_case1_j1 at (k, k−1)) + the (k−1)-q-front subcases, CASE-2 via prop213_step1
at (k, k−1), then A(k)@w via lk_induction (mirror main2T_of_g5T) — theorem_A's
span at weight w uses A(w)@w + the T-membership bridge + Counting.theorem_A_of_span.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
set_option autoImplicit false

/-- The generic level-`k` dispatch step: `m` is a recursion call from `s` iff
prefix-`k` drops or stays with Init-growth. -/
def MainkStep (k q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+) : Prop :=
  psum m k < psum s k ∨ (psum m k = psum s k ∧ InitLt q s m)

/-- From the Step-1 member facts (prefix-k < S or ≤ S with Init-growth) to the
dispatch step. -/
lemma mk_member_step (k q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (h : psum m k < psum s k ∨ (psum m k ≤ psum s k ∧ InitLt q s m)) :
    MainkStep k q s m := by
  rcases h with hlt | hrest
  · exact Or.inl hlt
  · rcases hrest with ⟨hle, hinit⟩
    by_cases hlt : psum m k < psum s k
    · exact Or.inl hlt
    · right
      constructor
      · omega
      · exact hinit

/-- The carrier of weight-`w` tuples (any depth). -/
abbrev LkCarrier (w : ℕ) := { p : (Σ r : ℕ, Fin r → ℕ+) // weight p.1 p.2 = w }

/-- The measure: (psum-k, M − 1 − initVal), M = (q+2)^(w+1), in the lex product. -/
noncomputable def lkμ (k q w : ℕ) (t : LkCarrier w) : ℕ ×ₗ ℕ :=
  (psum t.1.2 k, (q + 2) ^ (w + 1) - 1 - initVal q w t.1.2)

/-- Prefix-k drop ⟹ measure drop (first coordinate). -/
lemma lkμ_lt_of_psum_lt (k q w : ℕ) {t u : LkCarrier w}
    (h : psum u.1.2 k < psum t.1.2 k) : lkμ k q w u < lkμ k q w t := by
  rw [Prod.Lex.lt_iff]
  left
  exact h

/-- Equal prefix + Init-growth ⟹ measure drop (second coordinate). -/
lemma lkμ_lt_of_psum_eq_initLt (k q w : ℕ) {t u : LkCarrier w}
    (heq : psum u.1.2 k = psum t.1.2 k) (hlex : InitLt q t.1.2 u.1.2) :
    lkμ k q w u < lkμ k q w t := by
  rw [Prod.Lex.lt_iff]
  right
  constructor
  · exact heq
  · have hiv : initVal q w t.1.2 < initVal q w u.1.2 := initVal_lex_lt q w t.1.2 t.2 u.1.2 u.2 hlex
    have hMt : initVal q w t.1.2 < (q + 2) ^ (w + 1) := initVal_lt_pow q w t.1.2 t.2
    have hMu : initVal q w u.1.2 < (q + 2) ^ (w + 1) := initVal_lt_pow q w u.1.2 u.2
    have hivM1 : initVal q w t.1.2 < (q + 2) ^ (w + 1) - 1 := by
      have hle : initVal q w u.1.2 ≤ (q + 2) ^ (w + 1) - 1 := Nat.le_sub_one_of_lt hMu
      omega
    dsimp [lkμ]
    exact Nat.sub_lt_sub_left hivM1 hiv

/-- ★ Well-foundedness of the level-k dispatch (generic k). -/
theorem maink_step_wf (k q w : ℕ) :
    WellFounded (fun m s : LkCarrier w => MainkStep k q s.1.2 m.1.2) := by
  refine Subrelation.wf ?_ (InvImage.wf (lkμ k q w) wellFounded_lt)
  intro m s h
  rcases h with hlt | heq
  · exact lkμ_lt_of_psum_lt k q w hlt
  · exact lkμ_lt_of_psum_eq_initLt k q w heq.1 heq.2

/-- ★ The level-k recursion principle (generic k): `P` holds for every
weight-`w` tuple if each step `P(s)` follows from `P` on dispatch-calls `m`. -/
theorem lk_induction (k q w : ℕ) (hwf : WellFounded (fun m s : LkCarrier w => MainkStep k q s.1.2 m.1.2))
    (P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop)
    (hstep : ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      (∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
          MainkStep k q s m → P r' m hm) → P r s hw) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw := by
  classical
  let Q : LkCarrier w → Prop := fun t => P t.1.1 t.1.2 t.2
  have hfix : ∀ t : LkCarrier w, Q t := by
    exact WellFounded.fix hwf (fun t ih => by
      dsimp [Q]
      refine hstep t.1.1 t.1.2 t.2 ?_
      intro r' m hm hstepm
      exact ih ⟨⟨r', m⟩, hm⟩ hstepm)
  intro r s hw
  exact hfix ⟨⟨r, s⟩, hw⟩

/-- ★ The level-k in-domain trichotomy (generic k, k ≥ 1): a (k−1)-adm
∧ ¬k-adm tuple (q ≥ 2) is a CASE-1 tuple (depth ≥ k, k-th entry > q)
or a CASE-2 depth-k form (entries 1..k−1 ≤ q, last = q). -/
lemma levelk_inDomain_cases (k q : ℕ) (hq : 2 ≤ q) (hk1 : 1 ≤ k) {r : ℕ} (s : Fin r → ℕ+)
    (hkminus1 : kAdmissible q s (k - 1)) (hnot : ¬ kAdmissible q s k) :
    (k ≤ r ∧ q < pad0 s (k - 1)) ∨
      (r = k ∧ (∀ x : ℕ, x < k - 1 → pad0 s x ≤ q) ∧ pad0 s (k - 1) = q) := by
  classical
  have hdg : k ≤ r := depth_ge_of_not_adm q s hk1 hkminus1 hnot
  by_cases hAk : ∀ x : ℕ, x < k → pad0 s x ≤ q
  · -- cond1 at level k holds: ¬k-adm forces the depth-form witness
    have hw : ∃ hr1 : 1 ≤ r,
        r ≤ k ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧ (s ⟨r - 1, by omega⟩ : ℕ) = q := by
      by_contra hw'
      apply hnot
      exact ⟨hAk, hw'⟩
    rcases hw with ⟨hr1, hrkw, hall, hlast⟩
    right
    have hrk : r = k := by omega
    refine ⟨hrk, ?_, ?_⟩
    · intro x hx
      have hxr : x < r - 1 := by omega
      exact hall x hxr
    · subst r
      have hpv : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : k - 1 < k)
      rw [hpv]
      exact hlast
  · push_neg at hAk
    rcases hAk with ⟨x, hxk, hgt⟩
    have hx : x = k - 1 := by
      have hxge : k - 1 ≤ x := by
        by_contra hx'
        have hxsmall : x < k - 1 := by omega
        have hle := hkminus1.1 x hxsmall
        omega
      omega
    subst x
    left
    exact ⟨hdg, hgt⟩
end ZagierHoffmanPositiveChar
