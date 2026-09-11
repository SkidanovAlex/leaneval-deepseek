import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Multi
import Submission.MultiMass
import Submission.MultiW2
import Submission.DiscretLvl

/-!
# TASK (child): prove ALL lemmas in this file (no gaps may remain).  Statements are fixed;
# add helper lemmas as needed.  This is the pure ℝ/ℕ analysis of the level-map `lvl` from
# `Submission.DiscretLvl` (READ IT FIRST: `lvl`, `levelIdx`, `levelIdx_spec/le/lt/ge`,
# `level_error`, `lvl_of_unique`, `lvl_error` are PROVEN there and reusable).
#
# `lvl ε L v : ℕ = ∑ k ∈ range (L+1), (if (k:ℝ)*ε ≤ v ∧ v < ((k+1:ℕ):ℝ)*ε then k else 0)`
# is the level of the real value v on the grid of mesh ε over levels 0..L.
# The four lemmas below state: values never exceed L; for a level 1 ≤ k ≤ L the value is k
# exactly on the interval [kε,(k+1)ε); out of range (above (L+1)ε or negative) the value is 0.
# PROOF HINTS: mimic the disjointness argument inside DiscretLvl.lvl_of_unique (its `hk'` block
# proves that for k' ≠ k at most one interval fires).  `lvl_le` may be proven by case analysis on
# whether v lies in [0,(L+1)ε) (use lvl_of_unique with k := levelIdx and levelIdx_le) and outside
# (all terms vanish, e.g. split off range L+1... simplest: prove `lvl_le` from the stronger
# statement `lvl ε L v ≤ L` by induction-free interval counting: show by_cases hvlt : v < (L+1)ε:
#   - if v < 0: all terms 0.
#   - if 0 ≤ v < (L+1)ε: lvl = levelIdx ≤ L (lvl_of_unique + levelIdx_le + levelIdx_ge + lt).
#   - if (L+1)ε ≤ v: all interval conditions false: prove each term is 0 and lvl = 0.
#   (You may split v < 0 / v ≥ 0 first and use `lt_or_ge`/`le_or_gt` gymnastics; lemmas like
#    `lvl_neg_zero` and `lvl_top_zero` below ARE the out-of-range facts, so prove them FIRST and
#    reuse them inside `lvl_le`.)
#   For "all terms vanish" use: k ≤ L ⟹ (k+1:ℝ)*ε ≤ (L+1:ℝ)*ε for 0 ≤ ε, so v ≥ (L+1)ε ⟹
#   ¬(v < (k+1)ε); and v < 0 ⟹ ¬((k:ℝ)*ε ≤ v) when 0 ≤ ε.
# `lvl_interval`: both directions: (⇒) if lvl = k ≥ 1 then the k-th interval fires: argue via the
#   disjointness/at-most-one-interval property and positivity of the summands (any fired interval
#   j ≠ k would force lvl ≥ ... : show if j fires with j ≠ k then lvl ≥ j + (k ≥ 1)...: simpler:
#   lvl = k ⟹ SOME interval j fires with j = k: since lvl = Σ over fired j's of j and all fired
#   values are nonneg with at most one firing... prove at-most-one-fires first as a helper
#   `at_most_one_interval` and then lvl is either 0 or the value of the (unique) firing interval,
#   from which both directions are immediate.
#   (⇐) if the k-th interval fires then (at most one fires and value = k): lvl_of_unique applied
#   with that k works directly: lvl_of_unique (hε0) L v hk h1 h2 : lvl ε L v = k.
# `lvl_top_zero`: v ≥ (L+1)ε: every summand vanishes.
# `lvl_neg_zero`: v < 0: every summand vanishes (with 0 ≤ ε: (k:ℝ)*ε≤v impossible as (k:ℝ)*ε≥0).
# Use `norm_num`, `nlinarith`, `omega`, `ring`, `simpa`, `Finset.sum_eq_zero`.  Beware casts:
#   `((k + 1 : ℕ) : ℝ)` vs `((k : ℝ) + 1)`: they are equal by norm_num but NOT defeq for simp;
#   insert `norm_num`/`exact_mod_cast` where needed.  Keep everything in namespace
#   Submission.DiscretLvl (add your lemmas THERE so they see lvl's API).  Do not rename the four
#   fixed lemmas.  No new imports.  No sorries at the end (build must pass).
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators NNReal

namespace Submission

namespace DiscretLvl

/-- negative values give level 0 -/
lemma lvl_neg_zero {ε : ℝ} (hε : 0 < ε) (L : ℕ) (v : ℝ) (hv : v < 0) : lvl ε L v = 0 := by
  unfold lvl
  apply Finset.sum_eq_zero
  intro k hk
  have hke : 0 ≤ (k : ℝ) * ε := mul_nonneg (by exact_mod_cast (Nat.zero_le k)) (le_of_lt hε)
  have hnot : ¬ ((k : ℝ) * ε ≤ v ∧ v < ((k + 1 : ℕ) : ℝ) * ε) := by
    intro hh
    exact (not_le_of_gt hv) (le_trans hke hh.1)
  rw [if_neg hnot]

/-- out of range above: the level is 0 -/
lemma lvl_top_zero {ε : ℝ} (hε : 0 < ε) (L : ℕ) (v : ℝ)
    (hv : ((L + 1 : ℕ) : ℝ) * ε ≤ v) : lvl ε L v = 0 := by
  unfold lvl
  apply Finset.sum_eq_zero
  intro k hk
  have hklt : k < L + 1 := Finset.mem_range.mp hk
  have hkle : k ≤ L := by omega
  have hkc : ((k + 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ hkle)
  have hcm : ((k + 1 : ℕ) : ℝ) * ε ≤ ((L + 1 : ℕ) : ℝ) * ε :=
    mul_le_mul_of_nonneg_right hkc (le_of_lt hε)
  have hnot : ¬ ((k : ℝ) * ε ≤ v ∧ v < ((k + 1 : ℕ) : ℝ) * ε) := by
    intro hh
    have hlt : v < ((L + 1 : ℕ) : ℝ) * ε := lt_of_lt_of_le hh.2 hcm
    exact (not_le_of_gt hlt) hv
  rw [if_neg hnot]

/-- level values never exceed L -/
lemma lvl_le {ε : ℝ} (hε : 0 < ε) (L : ℕ) (v : ℝ) : lvl ε L v ≤ L := by
  by_cases hvneg : v < 0
  · have hl : lvl ε L v = 0 := lvl_neg_zero hε L v hvneg
    omega
  · have hv0 : 0 ≤ v := le_of_not_gt hvneg
    by_cases hvtop : ((L + 1 : ℕ) : ℝ) * ε ≤ v
    · have hl : lvl ε L v = 0 := lvl_top_zero hε L v hvtop
      omega
    · have hvlt : v < ((L + 1 : ℕ) : ℝ) * ε := lt_of_not_ge hvtop
      have h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε := by
        refine ⟨L, le_rfl, ?_⟩
        simpa using hvlt
      have hge : (levelIdx ε L v : ℝ) * ε ≤ v := levelIdx_ge ε L v hv0 h
      have hle : levelIdx ε L v ≤ L := levelIdx_le ε L v h
      have hlt : v < (levelIdx ε L v + 1 : ℕ) * ε := levelIdx_lt ε L v h
      have hl : lvl ε L v = levelIdx ε L v := by
        apply lvl_of_unique (le_of_lt hε) L v hle hge
        simpa using hlt
      calc
        lvl ε L v = levelIdx ε L v := hl
        _ ≤ L := hle

/-- (k ≥ 1) the level equals k exactly on the interval [kε,(k+1)ε) -/
lemma lvl_interval {ε : ℝ} (hε : 0 < ε) (L : ℕ) (v : ℝ) {k : ℕ} (hk0 : 1 ≤ k) (hk : k ≤ L) :
    lvl ε L v = k ↔ ((k : ℝ) * ε ≤ v ∧ v < ((k + 1 : ℕ) : ℝ) * ε) := by
  constructor
  · intro hl
    by_cases hvneg : v < 0
    · have hl0 : lvl ε L v = 0 := lvl_neg_zero hε L v hvneg
      omega
    · have hv0 : 0 ≤ v := le_of_not_gt hvneg
      by_cases hvtop : ((L + 1 : ℕ) : ℝ) * ε ≤ v
      · have hl0 : lvl ε L v = 0 := lvl_top_zero hε L v hvtop
        omega
      · have hvlt : v < ((L + 1 : ℕ) : ℝ) * ε := lt_of_not_ge hvtop
        have h : ∃ j : ℕ, j ≤ L ∧ v < (j + 1 : ℕ) * ε := by
          refine ⟨L, le_rfl, ?_⟩
          simpa using hvlt
        have hge : (levelIdx ε L v : ℝ) * ε ≤ v := levelIdx_ge ε L v hv0 h
        have hle : levelIdx ε L v ≤ L := levelIdx_le ε L v h
        have hlt : v < (levelIdx ε L v + 1 : ℕ) * ε := levelIdx_lt ε L v h
        have hlid : lvl ε L v = levelIdx ε L v := by
          apply lvl_of_unique (le_of_lt hε) L v hle hge
          simpa using hlt
        have hkeq : levelIdx ε L v = k := by
          rw [hlid] at hl
          exact hl
        constructor
        · simpa [hkeq] using hge
        · simpa [hkeq] using hlt
  · intro hf
    rcases hf with ⟨h1, h2⟩
    exact (lvl_of_unique (le_of_lt hε) L v hk h1 h2)

end DiscretLvl
end Submission
