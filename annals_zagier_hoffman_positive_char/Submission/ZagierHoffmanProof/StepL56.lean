import Submission.ZagierHoffmanProof.StepL55
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L56: A(2)@w — the level-2 branch lemmas (SESSION 199, warm-up + classification)

Goal (SESSION 199): instantiate StepL55's `l2_induction` with
`P(r s hw) := AdmExpT F w 2 s` to obtain A(2)@w for every w.  The per-step
dispatch needs the in-domain branch lemmas collected here (all sorry-free):

  • ★ inDomain2_cases (q hq s h1 hn2) : (2 ≤ r ∧ q < pad0 s 1) ∨ (r = 2 ∧ pad0 s 1 = q)
      — the level-2 in-domain classification: a 1-adm ¬2-adm tuple is a CASE-1
      tuple (depth ≥ 2, second entry > q — its cond1 at x = 1 fails) or a CASE-2
      tuple (depth 2, second entry = q — the cond2 witness fires; depth ≥ 2 by
      depth_ge_of_not_adm);
  • pad0_zero_pos / A2_self (2-adm → admExpT_self);
  • ★ A2_case2 (w s hw hr2 hp1 hs1q) : AdmExpT F w 2 s — the CASE-2 branch for
      s₁ < q (depth-2 (s₁, q)): identify s = pair s₁ (qExp F) via
      tuple_two_eq_of_pad0 (StepL54), apply case2_level2 (both members 2-adm, NO
      recursion), transport the weight parameter w = (s₁:ℕ) + q.

ADDED (same session): ★ A2_not_one_adm (the ¬1-adm warm-up: H1_expT + per-output
self/in-domain dispatch — provable given the in-domain handler as a hypothesis) and
★ A2_with_main2 (the A(2)-scaffold: every weight-w tuple expands at level 2 given
the in-domain handler `main2` — by_cases 2-adm (A2_self) / ¬2-adm: 1-adm (main2) /
¬1-adm (A2_not_one_adm)).  So A(2)@w is reduced to MAIN(2): prove the in-domain
handler `main2` by StepL55's l2_induction.

REMAINING (SESSION 200): the CASE-1 j = 1 branch (s₁ < q < s₂): instantiate
prop212_step1 at k = 2, j = 1; repackage the (a-side ≠ u / type-2 / type-3)
members as an AdmExpT Step-1 identity with per-member dispatch data — type-1/type-2:
prefix-2 < psum s 2 (prop212's conjuncts); type-3: prefix-2 ≤ psum s 2 with front
growth pad0 0 = s₁+1 at position 0 (type3_sjadd_one_at at j = 1), so headVal grows
and l2_member_lt (StepL55) gives the termination obligation — dispatch 2-adm members
by admExpT_self and ¬2-adm members by the recursion; splice with admExpT_combine.
Then A(2)@w = l2_induction over in-domain tuples with this step + A2_case2 +
A2_self + the ¬1-adm (H1_expT) and 2-adm cases; theorem_A(w) via the StepL54 tail.
OPEN SEPARATE ITEMS (do not block this step): the j = 0 chains for (q,q) and
(q, s₂>q) (G5 — reachable at weight w ≥ 2q), and the m ≥ 3 β-design.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable

/-- ★ The level-2 in-domain classification: a 1-adm, non-2-adm tuple is either a
CASE-1 tuple (depth ≥ 2, second entry > q) or a CASE-2 tuple (depth 2, second entry
= q). -/
lemma inDomain2_cases (q : ℕ) (hq : 2 ≤ q) {r : ℕ} (s : Fin r → ℕ+)
    (h1 : kAdmissible q s 1) (hn2 : ¬ kAdmissible q s 2) :
    (2 ≤ r ∧ q < pad0 s 1) ∨ (r = 2 ∧ pad0 s 1 = q) := by
  classical
  have hdg : 2 ≤ r := depth_ge_of_not_adm q s (by omega : 1 ≤ 2) h1 hn2
  by_cases hA2 : ∀ x : ℕ, x < 2 → pad0 s x ≤ q
  · -- cond1 at level 2 holds: ¬2-adm forces the cond2 witness
    have hw : ∃ hr1 : 1 ≤ r,
        r ≤ 2 ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧ (s ⟨r - 1, by omega⟩ : ℕ) = q := by
      by_contra hw'
      apply hn2
      exact ⟨hA2, hw'⟩
    rcases hw with ⟨hr1, hr2w, hall, hlast⟩
    right
    have hr2 : r = 2 := by omega
    refine ⟨hr2, ?_⟩
    subst r
    have hp1v : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 2)
    rw [hp1v]
    exact hlast
  · push_neg at hA2
    rcases hA2 with ⟨x, hx2, hgt⟩
    have hx01 : x = 0 ∨ x = 1 := by omega
    left
    rcases hx01 with hx0 | hx1
    · subst x
      have h01 : pad0 s 0 ≤ q := h1.1 0 (by omega)
      omega
    · subst x
      refine ⟨hdg, ?_⟩
      by_cases hr1c : r = 1
      · subst r
        have hp : pad0 s 1 = 0 := pad0_of_ge s (by omega : 1 ≤ 1)
        omega
      · omega  -- r ≠ 1 with r ≥ 2? we already have hdg : 2 ≤ r; this branch unreachable? pad0 s 1 with r ≥ 2 = s₂... wait hgt is about pad0 s 1 directly


variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A nonempty tuple of positive weight has positive first entry. -/
lemma pad0_zero_pos {r : ℕ} (s : Fin r → ℕ+) (hr : 0 < r) : 0 < pad0 s 0 := by
  have hp0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s hr
  rw [hp0v]
  exact (s ⟨0, by omega⟩).pos

/-- A 2-admissible tuple is its own level-2 expansion. -/
theorem A2_self (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hw0 : 0 < w) (h2 : kAdmissible (Nat.card F) s 2) : AdmExpT F w 2 s := by
  classical
  have hr : 0 < r := weight_pos_hr s hw hw0
  exact admExpT_self F w 2 hr s hw h2

/-- ★ The level-2 CASE-2 branch: a depth-2 tuple (s₁, q) with s₁ < q expands at
level 2 via `case2_level2` (both members 2-adm — no recursion). -/
theorem A2_case2 (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hr2 : r = 2) (hp1 : pad0 s 1 = Nat.card F) (hs1q : pad0 s 0 < Nat.card F) :
    AdmExpT F w 2 s := by
  classical
  subst r
  let s₁ : ℕ+ := ⟨pad0 s 0, pad0_zero_pos s (by omega : 0 < 2)⟩
  have hp0' : pad0 s 0 = (s₁ : ℕ) := rfl
  have hp1' : pad0 s 1 = (qExp F : ℕ) := by
    change pad0 s 1 = Nat.card F
    exact hp1
  have hseq : s = pair s₁ (qExp F) := tuple_two_eq_of_pad0 s s₁ (qExp F) hp0' hp1'
  have hs₁q : (s₁ : ℕ) < Nat.card F := by
    change pad0 s 0 < Nat.card F
    exact hs1q
  have hw2 : weight 2 s = (s₁ : ℕ) + Nat.card F := by
    have hw2' : weight 2 s = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
      rw [weight_two]
    have hp0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 2)
    have hp1v : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 2)
    rw [hw2']
    change (s₁ : ℕ) + (s ⟨1, by omega⟩ : ℕ) = (s₁ : ℕ) + Nat.card F
    have hB : (s ⟨1, by omega⟩ : ℕ) = Nat.card F := by
      rw [← hp1v]
      exact hp1
    omega
  have hc2l : AdmExpT F ((s₁ : ℕ) + Nat.card F) 2 (pair s₁ (qExp F)) :=
    case2_level2 F s₁ hs₁q
  have hAt : AdmExpT F w 2 (pair s₁ (qExp F)) := by
    -- w = weight 2 s = (s₁:ℕ)+q
    have hweq : w = (s₁ : ℕ) + Nat.card F := by
      rw [← hw2]
      exact hw.symm
    simpa [hweq] using hc2l
  have hA : AdmExpT F w 2 (pair s₁ (qExp F)) := hAt
  rw [hseq]
  exact hA
/-- ★ The ¬1-adm branch of A(2)@w: a weight-w tuple with a first entry > q (or the
depth-1 q-form) expands at level 2 through `H1_expT` (level 1), with each 1-adm
output dispatched to its own level-2 expansion (self if 2-adm, otherwise the
in-domain handler `inDom`). -/
theorem A2_not_one_adm (w : ℕ) (hw0 : 0 < w) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hn1 : ¬ kAdmissible (Nat.card F) s 1)
    (inDom : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExpT F w 2 m) :
    AdmExpT F w 2 s := by
  classical
  have hr : 0 < r := weight_pos_hr s hw hw0
  have hA1T : AdmExpT F w 1 s := by
    have h1 := H1_expT F r hr s
    simpa [hw] using h1
  rcases hA1T with ⟨ι, finι, dep, hdep, c, a, hw', hadm', horder', hid⟩
  letI : Fintype ι := finι
  refine admExpT_combine F w 2 s dep hdep c a hid ?horder ?e
  · intro i ℓ hℓ
    exact horder' i ℓ (by omega : 1 ≤ ℓ)
  · intro i
    by_cases h2i : kAdmissible (Nat.card F) (c i) 2
    · have hdi : 0 < dep i := hdep i
      exact admExpT_self F w 2 hdi (c i) (hw' i) h2i
    · exact inDom (dep i) (c i) (hw' i) (hadm' i) h2i

/-- ★ A(2)@w from the level-2 MAIN recursion (in-domain handler): every weight-w
tuple expands at level 2 given the in-domain handler `main2`.  This is the final
A(2)-scaffold: the remaining task is MAIN(2) itself (the CASE-1 j=1 recursion + the
j = 0 G5 chains). -/
theorem A2_with_main2 (w : ℕ) (hw0 : 0 < w)
    (main2 : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 → AdmExpT F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExpT F w 2 s := by
  intro r s hw
  by_cases h2 : kAdmissible (Nat.card F) s 2
  · exact A2_self F w s hw hw0 h2
  · by_cases h1 : kAdmissible (Nat.card F) s 1
    · exact main2 r s hw h1 h2
    · exact A2_not_one_adm F w hw0 s hw h1 main2

end ZagierHoffmanPositiveChar
