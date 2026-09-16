import Submission.ZagierHoffmanProof.StepL51
import Submission.ZagierHoffmanProof.StepL53
import Submission.ZagierHoffmanProof.StepL45
import Submission.ZagierHoffmanProof.StepL36
import Submission.ZagierHoffmanProof.Counting

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L54: the theorem-A(w ≤ 3) vertical slice (SESSION 197)

TOP-LEVEL TARGET (see PLAN SESSION 197 INSTRUCTION): hH instances
`hH : ∀ ⦃r⦄ (s : Fin r → ℕ+), weight r s = w → AdmExp F w w s` for w = 1, 2, 3,
built from `H1_expT` (A(1), StepL51), `case2_level2` (A(2) CASE-2, StepL53) and the
weight = level collapse `kAdm_weight_iff_sub_one` (StepL45); then the theorem_A
span instances `𝒵 F w = span K (𝒯 F w)` via `theoremA_span_eq_of_H` (StepL36) plus
the rank bound via `Counting.theorem_A_of_span` — validating the whole theorem-A
tail machinery end-to-end on the smallest weights.

KEY MATHEMATICAL FACTS (SESSION 196 ADDENDUM): at weight w ≤ 3 the only
¬2-adm ∧ 1-adm tuples are the CASE-2 depth-2 forms (s₁, q) with s₁ < q
(= (1,2) at q = 2), handled by `case2_level2`; every ¬1-adm weight-w tuple is
handled by `H1_expT`; and a weight-w tuple is w-adm iff (w−1)-adm
(`kAdm_weight_iff_sub_one`), so level-w outputs can be re-used at level w−1 and
vice versa.

STATUS (SESSION 197, all sorry-free): the FULL w ≤ 3 vertical slice is proven —
  (classification) entry_le_weight, weight_zero, weight_one_cases,
    weight_two_cases, weight_three_cases, weight_pos_hr, two_entries_le_weight,
    one_adm_not_two_adm_weight_three (the only 1-adm ¬2-adm weight-3 tuple is the
    CASE-2 form (1,q)@q=2), tuple_two_eq_of_pad0 (a depth-2 tuple is fixed by its
    pad0 entries);
  (level lift) admExp_level_succ: an expansion at level k re-targets to level k+1
    when every output has weight k+1 (the weight = level collapse);
  (H-w on weight-w tuples, w ≤ 3) H1_weight_one, H2_weight_two,
    H3_weight_three (level-3 via A2_weight_three + the collapse), with the
    ¬1-adm inputs routed through H1_expT and the CASE-2 (1,q)@q=2 inputs through
    case2_level2;
  (theorem A instances) theoremA_span_weight_one/two/three
    (`𝒵 F w = span K (𝒯 F w)`, via theoremA_span_eq_of_H) and the full
    theoremA_weight_one/two/three (`+ Module.rank ≤ d F w`, via
    Counting.theorem_A_of_span) — the theorem-A tail validated end-to-end.
NOTE: the w ≤ 3 slice needs NO MAIN(2) CASE-1 recursion and NO G5 (j = 0) chain:
weight ≤ 3 forces every ¬2-adm ∧ 1-adm input into the case2_level2 CASE-2 class
(SESSION 196 ADDENDUM).  The next step toward theorem_A for all w is the general
Prop-3.2 recursion (MAIN(2)@general-w then MAIN(k), with G5 and the β-design).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable

/-- Every entry of a tuple is at most its weight. -/
lemma entry_le_weight {r : ℕ} (s : Fin r → ℕ+) (i : Fin r) :
    (s i : ℕ) ≤ weight r s := by
  classical
  have hle : (s i : ℕ) ≤ (∑ j : Fin r, (s j : ℕ)) := by
    exact Finset.single_le_sum (fun j hj => Nat.zero_le ((s j : ℕ))) (Finset.mem_univ i)
  simpa [weight] using hle

/-- The empty tuple has weight 0. -/
lemma weight_zero {s : Fin 0 → ℕ+} : weight 0 s = 0 := by
  simp [weight]

/-- A tuple of weight 1 has depth 1 and its entry is 1. -/
lemma weight_one_cases {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = 1) :
    r = 1 ∧ pad0 s 0 = 1 := by
  have hle : r ≤ 1 := by
    have hg := weight_ge_depth r s
    omega
  have hr0' : r ≠ 0 := by
    intro hr0
    subst r
    have hw0 : weight 0 s = 0 := weight_zero (s := s)
    omega
  have hr1 : r = 1 := by omega
  refine ⟨hr1, ?_⟩
  subst r
  have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 1)
  have hw1 : (s ⟨0, by omega⟩ : ℕ) = 1 := by
    have hs : weight 1 s = (s ⟨0, by omega⟩ : ℕ) := by
      change (∑ i : Fin 1, (s i : ℕ)) = (s ⟨0, by omega⟩ : ℕ)
      rw [Fin.sum_univ_one]
      change (s (0 : Fin 1) : ℕ) = (s ⟨0, by omega⟩ : ℕ)
      congr 1
    omega
  rwa [hp]

/-- A tuple of weight 2 is either the depth-1 tuple (2) or the depth-2 tuple (1,1). -/
lemma weight_two_cases {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = 2) :
    (r = 1 ∧ pad0 s 0 = 2) ∨ (r = 2 ∧ pad0 s 0 = 1 ∧ pad0 s 1 = 1) := by
  have hle : r ≤ 2 := by
    have hg := weight_ge_depth r s
    omega
  have hr0' : r ≠ 0 := by
    intro hr0
    subst r
    have hw0 : weight 0 s = 0 := weight_zero (s := s)
    omega
  by_cases hr2 : r = 2
  · subst r
    right
    refine ⟨rfl, ?_, ?_⟩
    · have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 2)
      have hw2 : weight 2 s = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
        rw [weight_two]
      have h1 : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
      have h2 : 1 ≤ (s ⟨1, by omega⟩ : ℕ) := (s ⟨1, by omega⟩).pos
      rw [hp]
      omega
    · have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 2)
      have hw2 : weight 2 s = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
        rw [weight_two]
      have h1 : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
      have h2 : 1 ≤ (s ⟨1, by omega⟩ : ℕ) := (s ⟨1, by omega⟩).pos
      rw [hp]
      omega
  · left
    have hr1 : r = 1 := by omega
    subst r
    refine ⟨rfl, ?_⟩
    have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 1)
    have hw1 : (s ⟨0, by omega⟩ : ℕ) = 2 := by
      have hs : weight 1 s = (s ⟨0, by omega⟩ : ℕ) := by
        change (∑ i : Fin 1, (s i : ℕ)) = (s ⟨0, by omega⟩ : ℕ)
        rw [Fin.sum_univ_one]
        change (s (0 : Fin 1) : ℕ) = (s ⟨0, by omega⟩ : ℕ)
        congr 1
      omega
    rwa [hp]

/-- A tuple of weight 3 has one of the four shapes (3), (1,2), (2,1), (1,1,1). -/
lemma weight_three_cases {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = 3) :
    (r = 1 ∧ pad0 s 0 = 3) ∨
    (r = 2 ∧ ((pad0 s 0 = 1 ∧ pad0 s 1 = 2) ∨ (pad0 s 0 = 2 ∧ pad0 s 1 = 1))) ∨
    (r = 3 ∧ pad0 s 0 = 1 ∧ pad0 s 1 = 1 ∧ pad0 s 2 = 1) := by
  have hle : r ≤ 3 := by
    have hg := weight_ge_depth r s
    omega
  have hr0' : r ≠ 0 := by
    intro hr0
    subst r
    have hw0 : weight 0 s = 0 := weight_zero (s := s)
    omega
  by_cases hr3 : r = 3
  · subst r
    right
    right
    refine ⟨rfl, ?_, ?_, ?_⟩
    · have hp : pad0 s 0 = (s (0 : Fin 3) : ℕ) := by
        simpa using (pad0_of_lt s (by omega : 0 < 3))
      have hw3 : (s (0 : Fin 3) : ℕ) + (s (1 : Fin 3) : ℕ) + (s (2 : Fin 3) : ℕ) = 3 := by
        simpa [weight, Fin.sum_univ_three] using hw
      have h1 : 1 ≤ (s (0 : Fin 3) : ℕ) := (s (0 : Fin 3)).pos
      have h2 : 1 ≤ (s (1 : Fin 3) : ℕ) := (s (1 : Fin 3)).pos
      have h3 : 1 ≤ (s (2 : Fin 3) : ℕ) := (s (2 : Fin 3)).pos
      rw [hp]
      omega
    · have hp : pad0 s 1 = (s (1 : Fin 3) : ℕ) := by
        simpa using (pad0_of_lt s (by omega : 1 < 3))
      have hw3 : (s (0 : Fin 3) : ℕ) + (s (1 : Fin 3) : ℕ) + (s (2 : Fin 3) : ℕ) = 3 := by
        simpa [weight, Fin.sum_univ_three] using hw
      have h1 : 1 ≤ (s (0 : Fin 3) : ℕ) := (s (0 : Fin 3)).pos
      have h2 : 1 ≤ (s (1 : Fin 3) : ℕ) := (s (1 : Fin 3)).pos
      have h3 : 1 ≤ (s (2 : Fin 3) : ℕ) := (s (2 : Fin 3)).pos
      rw [hp]
      omega
    · have hp : pad0 s 2 = (s (2 : Fin 3) : ℕ) := by
        simpa using (pad0_of_lt s (by omega : 2 < 3))
      have hw3 : (s (0 : Fin 3) : ℕ) + (s (1 : Fin 3) : ℕ) + (s (2 : Fin 3) : ℕ) = 3 := by
        simpa [weight, Fin.sum_univ_three] using hw
      have h1 : 1 ≤ (s (0 : Fin 3) : ℕ) := (s (0 : Fin 3)).pos
      have h2 : 1 ≤ (s (1 : Fin 3) : ℕ) := (s (1 : Fin 3)).pos
      have h3 : 1 ≤ (s (2 : Fin 3) : ℕ) := (s (2 : Fin 3)).pos
      rw [hp]
      omega
  · by_cases hr2 : r = 2
    · subst r
      right
      left
      refine ⟨rfl, ?_⟩
      have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 2)
      have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 2)
      have hw2 : (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) = 3 := by
        rw [← weight_two]
        simpa [weight] using hw
      have h1 : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
      have h2 : 1 ≤ (s ⟨1, by omega⟩ : ℕ) := (s ⟨1, by omega⟩).pos
      have h01 : (s ⟨0, by omega⟩ : ℕ) = 1 ∨ (s ⟨0, by omega⟩ : ℕ) = 2 := by omega
      rcases h01 with h | h
      · left
        constructor
        · rwa [hp0]
        · rw [hp1]
          omega
      · right
        constructor
        · rwa [hp0]
        · rw [hp1]
          omega
    · left
      have hr1 : r = 1 := by omega
      subst r
      refine ⟨rfl, ?_⟩
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 1)
      have hw1 : (s ⟨0, by omega⟩ : ℕ) = 3 := by
        have hs : weight 1 s = (s ⟨0, by omega⟩ : ℕ) := by
          change (∑ i : Fin 1, (s i : ℕ)) = (s ⟨0, by omega⟩ : ℕ)
          rw [Fin.sum_univ_one]
          change (s (0 : Fin 1) : ℕ) = (s ⟨0, by omega⟩ : ℕ)
          congr 1
        omega
      rwa [hp]
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A tuple of positive weight has positive depth. -/
lemma weight_pos_hr {r : ℕ} (s : Fin r → ℕ+) {w : ℕ} (hw : weight r s = w) (hw0 : 0 < w) :
    0 < r := by
  by_contra h
  have hr0 : r = 0 := by omega
  subst r
  have hw0' : weight 0 s = 0 := weight_zero (s := s)
  omega

/-- Lift an expansion at level `k` to level `k+1` when every output has weight `k+1`
(weight = level collapse: a weight-`(k+1)` tuple is `(k+1)`-adm iff `k`-adm,
`kAdm_sub_one_weight_eq`). -/
lemma admExp_level_succ (k : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = k + 1)
    (hA : AdmExp F (k + 1) k s) : AdmExp F (k + 1) (k + 1) s := by
  classical
  rcases hA with ⟨ι, finι, dep, hdep, c, a, hw', hadm', hid⟩
  letI : Fintype ι := finι
  refine ⟨ι, finι, dep, hdep, c, a, hw', ?_, hid⟩
  intro i
  have hkm : (k + 1) - 1 = k := by omega
  have hc : kAdmissible (Nat.card F) (c i) ((k + 1) - 1) := by
    simpa [hkm] using hadm' i
  exact kAdm_sub_one_weight_eq (Nat.card F) (c i) (by omega : 1 ≤ k + 1) (card_ge_two F)
    (hw' i) hc

/-- Every weight-2 tuple expands at level 2: (H_2) on weight-2 tuples. -/
theorem H2_weight_two (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = 2) :
    AdmExp F 2 2 s := by
  classical
  by_cases h2 : kAdmissible (Nat.card F) s 2
  · have hr : 0 < r := weight_pos_hr s hw (by omega : 0 < 2)
    exact admExp_self F 2 2 hr s hw h2
  · have hr : 0 < r := weight_pos_hr s hw (by omega : 0 < 2)
    have hA1T : AdmExpT F 2 1 s := by
      have h1 := H1_expT F r hr s
      simpa [hw] using h1
    have hA1 : AdmExp F 2 1 s := admExpT_to_AdmExp F 2 1 s hA1T
    exact admExp_level_succ F 1 s hw hA1
/-- Sum of two distinct entries is at most the weight. -/
lemma two_entries_le_weight {r : ℕ} (s : Fin r → ℕ+) {i j : Fin r} (hij : i ≠ j) :
    (s i : ℕ) + (s j : ℕ) ≤ weight r s := by
  classical
  have hsum : (∑ k : Fin r, (s k : ℕ)) =
      (∑ k ∈ (Finset.univ : Finset (Fin r)).erase i, (s k : ℕ)) + (s i : ℕ) := by
    rw [Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r))) (f := fun k : Fin r => (s k : ℕ))
      (a := i) (Finset.mem_univ i)]
  have hji : j ∈ (Finset.univ : Finset (Fin r)).erase i := by
    simp [hij.symm]
  have hle : (s j : ℕ) ≤ (∑ k ∈ (Finset.univ : Finset (Fin r)).erase i, (s k : ℕ)) := by
    exact Finset.single_le_sum (fun k hk => Nat.zero_le ((s k : ℕ))) hji
  change (s i : ℕ) + (s j : ℕ) ≤ (∑ k : Fin r, (s k : ℕ))
  rw [hsum]
  omega
/-- ★ The only 1-admissible, non-2-admissible tuple of weight 3 is the CASE-2
depth-2 form (1, q) with q = 2: `q = 2, r = 2, pad0 s 0 = 1, pad0 s 1 = 2`. -/
lemma one_adm_not_two_adm_weight_three (q : ℕ) (hq : 2 ≤ q) {r : ℕ} (s : Fin r → ℕ+)
    (hw : weight r s = 3) (h1 : kAdmissible q s 1) (hn2 : ¬ kAdmissible q s 2) :
    q = 2 ∧ r = 2 ∧ pad0 s 0 = 1 ∧ pad0 s 1 = 2 := by
  classical
  have hr : 0 < r := weight_pos_hr s hw (by omega)
  -- ¬2-adm forces the cond2 witness (cond1 cannot fail)
  have hw2w : ∃ hr1 : 1 ≤ r,
      r ≤ 2 ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧ (s ⟨r - 1, by omega⟩ : ℕ) = q := by
    by_cases hA2 : ∀ x : ℕ, x < 2 → pad0 s x ≤ q
    · by_contra hw2w'
      apply hn2
      exact ⟨hA2, hw2w'⟩
    · push_neg at hA2
      rcases hA2 with ⟨x, hx2, hgt⟩
      have hx01 : x = 0 ∨ x = 1 := by omega
      rcases hx01 with hx0 | hx1
      · subst x
        have h01 : pad0 s 0 ≤ q := h1.1 0 (by omega)
        omega
      · subst x
        by_cases hr1c : r = 1
        · subst r
          have hp : pad0 s 1 = 0 := pad0_of_ge s (by omega : 1 ≤ 1)
          omega
        · have hrge : 2 ≤ r := by omega
          have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
          have hgt' : q < (s ⟨1, by omega⟩ : ℕ) := by rwa [hp] at hgt
          have hle0 : (s ⟨0, by omega⟩ : ℕ) ≤ q := by
            have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
            rw [← hp0]
            exact h1.1 0 (by omega)
          have hs0pos : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
          have htwo : (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) ≤ weight r s := by
            exact two_entries_le_weight s
              (by intro h
                  have hv := congrArg (fun i : Fin r => (i : ℕ)) h
                  have hz : (0 : ℕ) = 1 := by
                    simpa using hv
                  omega)
          have hs2le : (s ⟨1, by omega⟩ : ℕ) ≤ 2 := by omega
          omega
  rcases hw2w with ⟨hr1, hr2, hle, hlast⟩
  have hr1' : r ≠ 1 := by
    intro hr1c
    subst r
    apply h1.2
    refine ⟨hr1, ?_, ?_, hlast⟩
    · omega
    · intro x hx
      omega
  have hr2' : r = 2 := by omega
  subst r
  have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 2)
  have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 2)
  have hlast' : pad0 s 1 = q := by rwa [hp1]
  have hw2' : (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) = 3 := by
    have hw' : weight 2 s = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
      rw [weight_two]
    omega
  have hs0pos : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
  have hq2 : q = 2 := by omega
  refine ⟨hq2, rfl, ?_, ?_⟩
  · omega
  · omega
/-- A depth-2 tuple is determined by its two entries (pad0 values). -/
lemma tuple_two_eq_of_pad0 (s : Fin 2 → ℕ+) (u v : ℕ+)
    (hp0 : pad0 s 0 = (u : ℕ)) (hp1 : pad0 s 1 = (v : ℕ)) : s = pair u v := by
  funext j
  by_cases hj0 : (j : ℕ) = 0
  · have hj : j = (0 : Fin 2) := Fin.ext (by simpa using hj0)
    rw [hj]
    change s (0 : Fin 2) = pair u v (0 : Fin 2)
    rw [pair]
    simp
    apply Subtype.ext
    exact hp0
  · have hj1 : (j : ℕ) = 1 := by
      have hlt : (j : ℕ) < 2 := j.isLt
      omega
    have hj : j = (1 : Fin 2) := Fin.ext (by simpa using hj1)
    rw [hj]
    change s (1 : Fin 2) = pair u v (1 : Fin 2)
    rw [pair]
    simp
    apply Subtype.ext
    exact hp1


/-- A 1-admissible weight-3 tuple expands at level 2: the only ¬2-adm one is the
CASE-2 form (1,q)@q=2, handled by `case2_level2`; the rest are 2-adm (self). -/
theorem A2_of_one_adm_weight_three {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = 3)
    (h1 : kAdmissible (Nat.card F) s 1) : AdmExp F 3 2 s := by
  classical
  by_cases h2 : kAdmissible (Nat.card F) s 2
  · have hr : 0 < r := weight_pos_hr s hw (by omega)
    exact admExp_self F 3 2 hr s hw h2
  · have hsh := one_adm_not_two_adm_weight_three (Nat.card F) (card_ge_two F) s hw h1 h2
    rcases hsh with ⟨hq2, hr2, hp0, hp1⟩
    subst r
    have hp0' : pad0 s 0 = (oneExp : ℕ) := by
      change pad0 s 0 = 1
      exact hp0
    have hp1' : pad0 s 1 = (qExp F : ℕ) := by
      change pad0 s 1 = Nat.card F
      omega
    have hseq : s = pair oneExp (qExp F) := tuple_two_eq_of_pad0 s oneExp (qExp F) hp0' hp1'
    have hs1q : (oneExp : ℕ) < Nat.card F := by
      change 1 < Nat.card F
      rw [hq2]
      omega
    have hw3eq : (oneExp : ℕ) + Nat.card F = 3 := by
      change 1 + Nat.card F = 3
      rw [hq2]
    have hc2l : AdmExpT F ((oneExp : ℕ) + Nat.card F) 2 (pair oneExp (qExp F)) :=
      case2_level2 F oneExp hs1q
    have hAt : AdmExpT F 3 2 (pair oneExp (qExp F)) := by
      simpa [hw3eq] using hc2l
    have hA : AdmExp F 3 2 (pair oneExp (qExp F)) := admExpT_to_AdmExp F 3 2 (pair oneExp (qExp F)) hAt
    rw [hseq]
    exact hA

/-- Every weight-3 tuple expands at level 2 (the 2-admissible inputs by self, the
¬1-adm ones through `H1_expT` + per-output `A2_of_one_adm_weight_three`). -/
theorem A2_weight_three (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = 3) : AdmExp F 3 2 s := by
  classical
  by_cases h2 : kAdmissible (Nat.card F) s 2
  · have hr : 0 < r := weight_pos_hr s hw (by omega)
    exact admExp_self F 3 2 hr s hw h2
  · by_cases h1 : kAdmissible (Nat.card F) s 1
    · exact A2_of_one_adm_weight_three F s hw h1
    · have hr : 0 < r := weight_pos_hr s hw (by omega)
      have hA1T : AdmExpT F 3 1 s := by
        have h1e := H1_expT F r hr s
        simpa [hw] using h1e
      have hA1 : AdmExp F 3 1 s := admExpT_to_AdmExp F 3 1 s hA1T
      rcases hA1 with ⟨ι, finι, dep, hdep, c, a, hw', hadm', hid⟩
      letI : Fintype ι := finι
      have e : ∀ i : ι, AdmExp F 3 2 (c i) := by
        intro i
        exact A2_of_one_adm_weight_three F (c i) (hw' i) (hadm' i)
      exact admExp_combine F 3 2 s dep hdep c a hid e

/-- ★ Every weight-3 tuple expands at level 3: (H_3) on weight-3 tuples. -/
theorem H3_weight_three (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = 3) : AdmExp F 3 3 s := by
  classical
  by_cases h3 : kAdmissible (Nat.card F) s 3
  · have hr : 0 < r := weight_pos_hr s hw (by omega)
    exact admExp_self F 3 3 hr s hw h3
  · have hA2 := A2_weight_three F r s hw
    exact admExp_level_succ F 2 s hw hA2
/-- Every weight-1 tuple expands at level 1: (H_1) on weight-1 tuples. -/
theorem H1_weight_one (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = 1) : AdmExp F 1 1 s := by
  classical
  have h1 : kAdmissible (Nat.card F) s 1 := by
    have hw1c := weight_one_cases s hw
    rcases hw1c with ⟨hr1, hp0⟩
    subst r
    constructor
    · intro x hx
      have hx0 : x = 0 := by omega
      subst x
      rw [hp0]
      have hq : 2 ≤ Nat.card F := card_ge_two F
      omega
    · intro hw2
      rcases hw2 with ⟨hr1', hrk, hall, hlast⟩
      have hp0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 1)
      have hval : (s ⟨0, by omega⟩ : ℕ) = 1 := by omega
      have hq2 : Nat.card F ≠ 1 := by
        have hq := card_ge_two F
        omega
      apply hq2
      rw [← hlast]
      exact hval
  have hr : 0 < r := weight_pos_hr s hw (by omega)
  exact admExp_self F 1 1 hr s hw h1

/-- The span half of theorem A at weight 1. -/
theorem theoremA_span_weight_one : 𝒵 F 1 = Submodule.span (RatFunc F) (𝒯 F 1) := by
  exact theoremA_span_eq_of_H F 1 (by omega) (fun ⦃r⦄ s hw => H1_weight_one F r s hw)

/-- The span half of theorem A at weight 2. -/
theorem theoremA_span_weight_two : 𝒵 F 2 = Submodule.span (RatFunc F) (𝒯 F 2) := by
  exact theoremA_span_eq_of_H F 2 (by omega) (fun ⦃r⦄ s hw => H2_weight_two F r s hw)

/-- The span half of theorem A at weight 3. -/
theorem theoremA_span_weight_three : 𝒵 F 3 = Submodule.span (RatFunc F) (𝒯 F 3) := by
  exact theoremA_span_eq_of_H F 3 (by omega) (fun ⦃r⦄ s hw => H3_weight_three F r s hw)


/-- Full theorem A at weight 1 (span equality + rank bound): the w ≤ 3 vertical
slice instance. -/
theorem theoremA_weight_one : 𝒵 F 1 = Submodule.span (RatFunc F) (𝒯 F 1) ∧
    Module.rank (RatFunc F) (𝒵 F 1) ≤ d F 1 := by
  exact theorem_A_of_span F ⟨1, by norm_num⟩ (theoremA_span_weight_one F)

/-- Full theorem A at weight 2 (span equality + rank bound): the w ≤ 3 vertical
slice instance. -/
theorem theoremA_weight_two : 𝒵 F 2 = Submodule.span (RatFunc F) (𝒯 F 2) ∧
    Module.rank (RatFunc F) (𝒵 F 2) ≤ d F 2 := by
  exact theorem_A_of_span F ⟨2, by norm_num⟩ (theoremA_span_weight_two F)

/-- Full theorem A at weight 3 (span equality + rank bound): the w ≤ 3 vertical
slice instance. -/
theorem theoremA_weight_three : 𝒵 F 3 = Submodule.span (RatFunc F) (𝒯 F 3) ∧
    Module.rank (RatFunc F) (𝒵 F 3) ≤ d F 3 := by
  exact theorem_A_of_span F ⟨3, by norm_num⟩ (theoremA_span_weight_three F)
end ZagierHoffmanPositiveChar
