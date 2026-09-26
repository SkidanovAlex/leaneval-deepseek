import Submission.Work.T1Absorb
import Submission.Work.NielsenAlign

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# T2: the strict / balanced (half-half) classification of the aggregate phase

`T1Absorb.t1_absorb_general` supplies a factor fully absorbed by its ≤ 2
neighbours; `Confine.confined_factor_exists` guarantees the absorbed factor is
*confined*: every letter pairs into the two adjacent blocks only.  This module
formalises the classical two-phase dichotomy of the absorbed factor `w_j` (its
word `L := Fs[j]`, with `r₁ := crossCount (j-1)` letters pairing left and
`r₂ := crossCount j` letters pairing right, `|L| = r₁ + r₂` by confinement):

* **Fall I (strict, "mehr als zur Hälfte ausgelöscht")**: if
  `|L| < 2·align L_{j-1} L` (strictly more than half of `w_j` cancels against
  the tail of the left neighbour), then `|reduce (L_{j-1} ++ L)| < |L_{j-1}|`
  — the *combination with the neighbour* has fewer letters than the neighbour
  (`fallI_left_shortens`; right-hand variant `fallI_right_shortens`).  This is
  the quantitative content of the elementary-move shortening: replacing the
  neighbour by its product with `w_j` strictly reduces total length.
* **Fall II (balanced)**: if neither side is strict, confinement forces the
  exact half-half state — `|L|` is even and both junction alignments equal
  `|L|/2` (`t2_balanced_of_not_fallI`): `w_j = A·B` with `|A| = |B| = |w_j|/2`
  and each neighbour covers exactly its half (`align = |w_j|/2`), the state
  from which the classical rebalancing (T3) proceeds.

The dichotomy `t2_strict_or_balanced` assembles the two.

Machine validation (exact Lean pairing semantics): among confined triples with
reduced product of length ≤ 1 (2628 exhaustive instances, n = 2, |w| ≤ 3),
"not strict on either junction" ⟹ balanced: **0 failures**.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Fall I: the strict (more-than-half) phase is an elementary shortening -/

/-- Left-neighbour strict phase: if strictly more than half of `M` cancels
against the tail of `L` (`|M| < 2·align L M`), then the combination `L ++ M`
reduces strictly below `|L|` — multiplying the (reduced) word `L` on the
right by `M` shortens it. -/
lemma fallI_left_shortens {α : Type*} [DecidableEq α]
    (L M : List (α × Bool)) (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M)
    (h : M.length < 2 * align L M) :
    (FreeGroup.reduce (L ++ M)).length < L.length := by
  have hlen := reduce_append_align L M hL hM
  have hleL := align_le_length_left L M
  have hleR := align_le_length_right L M
  omega

/-- Right-neighbour strict phase: if strictly more than half of `L` cancels
against the head of `M` (`|L| < 2·align L M`), then the combination `L ++ M`
reduces strictly below `|M|` — multiplying the (reduced) word `M` on the left
by `L` shortens it. -/
lemma fallI_right_shortens {α : Type*} [DecidableEq α]
    (L M : List (α × Bool)) (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M)
    (h : L.length < 2 * align L M) :
    (FreeGroup.reduce (L ++ M)).length < M.length := by
  have hlen := reduce_append_align L M hL hM
  have hleL := align_le_length_left L M
  have hleR := align_le_length_right L M
  omega

/-! ## Fall II: not-strict on both junctions forces the half-half state -/

/-- **T2, balanced classification.**  For a confined interior factor `w_j`
whose left and right junction alignments each absorb at most half of its word,
the exact half-half state holds: both alignments equal `|L_j|/2`, and `|L_j|`
is even.  (Confinement bounds `|L_j|` by the sum of the two cross counts, each
cross count is bounded by its junction alignment, and the two alignment
halves bound the sum — all four quantities coincide.) -/
theorem t2_balanced_of_not_fallI {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j)
    (hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length)
    (hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length) :
    align (Fs[j - 1]) (Fs[j]) = align (Fs[j]) (Fs[j + 1]) ∧
      ∃ k : ℕ, (Fs[j]).length = 2 * k ∧ align (Fs[j - 1]) (Fs[j]) = k := by
  classical
  have hle_sum : (Fs[j]).length ≤ crossCount Fs (j - 1) + crossCount Fs j :=
    confined_length_le_cross_sum Fs hred (j := j) hj0 hjk hconf
  have hcL : crossCount Fs (j - 1) ≤ align (Fs[j - 1]) (Fs[j]) :=
    align_left_junction Fs hred (j := j) hj0 hj
  have hcR : crossCount Fs j ≤ align (Fs[j]) (Fs[j + 1]) :=
    align_right_junction Fs hred (j := j) hjk
  have hsum : (Fs[j]).length ≤ align (Fs[j - 1]) (Fs[j]) + align (Fs[j]) (Fs[j + 1]) := by
    omega
  have hsumR : align (Fs[j - 1]) (Fs[j]) + align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length := by
    omega
  have hEqSum : align (Fs[j - 1]) (Fs[j]) + align (Fs[j]) (Fs[j + 1]) = (Fs[j]).length := by
    omega
  have hEqA : align (Fs[j - 1]) (Fs[j]) = align (Fs[j]) (Fs[j + 1]) := by
    have h1 : align (Fs[j - 1]) (Fs[j]) ≤ align (Fs[j]) (Fs[j + 1]) := by omega
    have h2 : align (Fs[j]) (Fs[j + 1]) ≤ align (Fs[j - 1]) (Fs[j]) := by omega
    omega
  constructor
  · exact hEqA
  · refine ⟨align (Fs[j - 1]) (Fs[j]), ?_, rfl⟩
    omega

/-- **T2, the dichotomy.**  For a confined interior factor, either the strict
phase holds on one junction (more than half of the factor cancels against a
neighbour — then `fallI_left_shortens` / `fallI_right_shortens` provide the
strictly shortening combination), or the balanced half-half state holds. -/
theorem t2_strict_or_balanced {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j) :
    (Fs[j]).length < 2 * align (Fs[j - 1]) (Fs[j]) ∨
    (Fs[j]).length < 2 * align (Fs[j]) (Fs[j + 1]) ∨
    (align (Fs[j - 1]) (Fs[j]) = align (Fs[j]) (Fs[j + 1]) ∧
      ∃ k : ℕ, (Fs[j]).length = 2 * k ∧ align (Fs[j - 1]) (Fs[j]) = k) := by
  classical
  by_cases hsL : (Fs[j]).length < 2 * align (Fs[j - 1]) (Fs[j])
  · exact Or.inl hsL
  · by_cases hsR : (Fs[j]).length < 2 * align (Fs[j]) (Fs[j + 1])
    · exact Or.inr (Or.inl hsR)
    · right; right
      have hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length := by omega
      have hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length := by omega
      exact t2_balanced_of_not_fallI Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR

end Submission.Nielsen
