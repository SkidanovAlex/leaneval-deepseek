import Submission.ZagierHoffmanProof.StepL94
import Submission.ZagierHoffmanProof.StepL92
import Submission.ZagierHoffmanProof.StepL90
import Submission.ZagierHoffmanProof.StepL88
import Submission.ZagierHoffmanProof.StepL86
import Submission.ZagierHoffmanProof.StepL82
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L95: ★ main3 — MAIN(3), the in-domain level-3 handler COMMITTED (SESSION 249)

theorem main3 (w : \u2115) (hw0 : 0 < w) : \u2200 r s hw,
    kAdmissible q s 2 \u2192 \u00ac kAdmissible q s 3 \u2192 AdmExpT F w 3 s
— every weight-w level-3 in-domain tuple (2-adm \u2227 \u00ac3-adm) expands at level 3.
PROOF (l3_induction of StepL82; per-step dispatch by level3_inDomain_cases):
  CASE-1 (3 \u2264 r \u2227 q < pad0 s 2), j-split on pad0 s 1 = q:
    · pad0 s 1 = q: pad0 s 0 = q \u2192 g53_case1_step (j=0, StepL86); pad0 s 0 < q
      \u2192 main3_case1_j1 (j=1, StepL88);
    · pad0 s 1 < q \u2192 main3_case1_j2 (j=2, StepL89);
  CASE-2 (r = 3 \u2227 pad0 s 2 = q \u2227 entries \u2264 q): subst r; s = (a,b,q):
    · b < q \u2192 case3_leaf_j2 (StepL90);
    · b = q: a = q \u2192 g53_case2_qqq (the (q,q,q) j=0 leaf, StepL94);
      a < q \u2192 main3_case2_j1 (StepL92);
with rec := the l3-induction IH (pad0→value conversions via pad0_of_lt +
kAdmissible.pad0_le + lt_of_le_of_ne).  ALL SEVEN LEAVES CLOSED; main3 is the
in-domain core that A(3)@w / the H_k tower assembly consumes next.
NEXT: A3_with_main3-scaffold + the H_k tower assembly (level-by-level main(k) +
admissibility descent), then theorem_A's span via Counting.theorem_A_of_span.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


/-- ★ MAIN(3): the in-domain handler at level 3 — all seven leaves CLOSED. -/
theorem main3 (w : ℕ) (hw0 : 0 < w) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 2 → ¬ kAdmissible (Nat.card F) s 3 →
      AdmExpT F w 3 s := by
  classical
  let P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop :=
    fun r s hw => kAdmissible (Nat.card F) s 2 → ¬ kAdmissible (Nat.card F) s 3 →
      AdmExpT F w 3 s
  change ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw
  refine l3_induction (Nat.card F) w (main3_step_wf (Nat.card F) w) P ?_
  intro r s hw rec h2 hn3
  have hcases := level3_inDomain_cases (Nat.card F) (card_ge_two F) s h2 hn3
  rcases hcases with hc1 | hc2
  · -- CASE-1: 3 ≤ r ∧ q < pad0 s 2
    rcases hc1 with ⟨hcase3, hbigp⟩
    by_cases hs1e : pad0 s 1 = Nat.card F
    · -- s₁ = q : subcase s₀ = q (j=0 via g53_case1_step) / s₀ < q (j=1 prop212)
      by_cases hs0e : pad0 s 0 = Nat.card F
      · -- j=0 (all-q front (q,q), s₂ > q): the g53 chain splice with main3's own
        -- recursion IH (every ¬3-adm member is 2-adm with a strict prefix-3 drop).
        exact g53_case1_step F w r s hw hcase3 hbigp hs0e hs1e rec
      · -- j=1 (s₀ < q, s₁ = q): splice via main3_case1_j1
        have hs0lt : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by
          have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
          rw [← hp]
          exact lt_of_le_of_ne (kAdmissible.pad0_le h2 0 (by omega)) hs0e
        have hs1v : (s ⟨1, by omega⟩ : ℕ) = Nat.card F := by
          have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
          rw [← hp]
          exact hs1e
        have hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ) := by
          have hp : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < r)
          rw [← hp]
          exact hbigp
        exact main3_case1_j1 F w r s hw hcase3 hbigv hs0lt hs1v rec
    · -- s₁ < q : j=2 via main3_case1_j2
      have hs0v : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F := by
        have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
        rw [← hp]
        exact kAdmissible.pad0_le h2 0 (by omega)
      have hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F := by
        have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
        rw [← hp]
        exact lt_of_le_of_ne (kAdmissible.pad0_le h2 1 (by omega)) hs1e
      have hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ) := by
        have hp : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < r)
        rw [← hp]
        exact hbigp
      exact main3_case1_j2 F w r s hw hcase3 hbigv hs0v hs1q rec
  · -- CASE-2: r = 3 ∧ (a,b,q) with a,b ≤ q
    rcases hc2 with ⟨hr3, hleq2, hq2p⟩
    subst hr3
    -- s : Fin 3 → ℕ+ ; hw : weight 3 s = w
    let a : ℕ+ := s ⟨0, by omega⟩
    let b : ℕ+ := s ⟨1, by omega⟩
    have h0v : (s ⟨0, by omega⟩ : ℕ) = (a : ℕ) := rfl
    have h1v : (s ⟨1, by omega⟩ : ℕ) = (b : ℕ) := rfl
    have h2v : (s ⟨2, by omega⟩ : ℕ) = Nat.card F := by
      have hp : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < 3)
      omega
    have hseq : s = consVec a (pair b (qExp F)) := by
      apply tuple3_eq_consVec_pair (c := qExp F)
      · exact h0v
      · exact h1v
      · rw [h2v]
        rw [show (qExp F : ℕ) = Nat.card F by rfl]
    have ha : (a : ℕ) ≤ Nat.card F := by
      have hle := kAdmissible.pad0_le h2 0 (by omega)
      have hp : pad0 s 0 = (a : ℕ) := by
        simpa [a] using (pad0_of_lt s (by omega : 0 < 3))
      rw [← hp]
      exact hle
    by_cases hbq : (b : ℕ) = Nat.card F
    · -- b = q : a = q → g53_case2_qqq (the (q,q,q) j=0 leaf) / a < q → main3_case2_j1
      have h1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F := by
        exact hbq
      have h2q : (s ⟨2, by omega⟩ : ℕ) = Nat.card F := by
        have hp : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < 3)
        omega
      by_cases haq : (s ⟨0, by omega⟩ : ℕ) = Nat.card F
      · -- (q,q,q): the j=0 leaf (all members 2-adm weight-3q with the strict prefix-3 drop)
        exact g53_case2_qqq F w s hw haq h1q h2q rec
      · -- (a,q,q) with a < q: the j=1 splice
        have hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by
          have hle := kAdmissible.pad0_le h2 0 (by omega)
          have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 3)
          rw [hp] at hle
          exact lt_of_le_of_ne hle haq
        exact main3_case2_j1 F w s hw h2 hsj h1q h2q rec
    · -- b < q : the case3_leaf_j2 leaf (no recursion)
      have hb : (b : ℕ) < Nat.card F := by
        have hle := kAdmissible.pad0_le h2 1 (by omega)
        have hp : pad0 s 1 = (b : ℕ) := by
          simpa [b] using (pad0_of_lt s (by omega : 1 < 3))
        rw [hp] at hle
        exact lt_of_le_of_ne hle hbq
      have hw3 : weight 3 s = (a : ℕ) + (b : ℕ) + Nat.card F := by
        rw [hseq]
        rw [weight_consVec]
        rw [weight_pair]
        change (a : ℕ) + ((b : ℕ) + (qExp F : ℕ)) = (a : ℕ) + (b : ℕ) + Nat.card F
        rw [show (qExp F : ℕ) = Nat.card F by rfl]
        omega
      have hleaf := case3_leaf_j2 F a b ha hb
      have hwab : (a : ℕ) + (b : ℕ) + Nat.card F = w := by
        rw [← hw]
        exact hw3.symm
      rw [hseq, ← hwab]
      exact hleaf
end ZagierHoffmanPositiveChar
