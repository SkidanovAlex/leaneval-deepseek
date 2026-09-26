import Mathlib
import Submission.Work.Sweep.LevelCount

/-!
# Additivity of the level count over a countable disjoint union

`levelCount f s y` is the (extended) number of points of `s` at which `f` takes the
value `y`.  This file proves that it is countably additive over a pairwise disjoint
family of sets: the level count of `⋃ n, A n` is the `tsum` of the level counts of
the parts.

The proof is purely combinatorial.  Writing `B n = A n ∩ f ⁻¹' {y}`, the extended
cardinality `(⋃ n, B n).encard` is the supremum of the cardinalities of the finite
subsets of the union, which is exhibited as a double `tsum` of indicator functions.
Concretely we show the identity of indicator functions
`(⋃ n, B n).indicator 1 = ∑' n, (B n).indicator 1`
(pairwise disjointness makes the sum have at most one nonzero term), then swap the
two `tsum`s with `ENNReal.tsum_comm`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.Sweep.LevelCountTsum

/-- The extended cardinality of a pairwise disjoint countable union is the sum of
the extended cardinalities of its parts. -/
lemma encard_iUnion_eq_tsum {α : Type*} (B : ℕ → Set α)
    (h : Pairwise (Function.onFun Disjoint B)) :
    ((⋃ n, B n).encard : ℝ≥0∞) = ∑' n, ((B n).encard : ℝ≥0∞) := by
  have hpoint : ∀ a, (⋃ n, B n).indicator (fun _ => (1 : ℝ≥0∞)) a
      = ∑' n, (B n).indicator (fun _ => (1 : ℝ≥0∞)) a := by
    intro a
    by_cases ha : a ∈ ⋃ n, B n
    · rw [Set.indicator_of_mem ha]
      obtain ⟨n₀, hn₀⟩ := Set.mem_iUnion.mp ha
      rw [tsum_eq_single n₀]
      · rw [Set.indicator_of_mem hn₀]
      · intro b hb
        rw [Set.indicator_of_notMem]
        intro hmem
        exact (Set.disjoint_left.mp (h hb) hmem) hn₀
    · rw [Set.indicator_of_notMem ha]
      have hz : ∀ n, (B n).indicator (fun _ => (1 : ℝ≥0∞)) a = 0 := by
        intro n
        rw [Set.indicator_of_notMem]
        intro hmem
        exact ha (Set.mem_iUnion.mpr ⟨n, hmem⟩)
      simp [hz]
  calc ((⋃ n, B n).encard : ℝ≥0∞)
      = ∑' _ : (⋃ n, B n), (1 : ℝ≥0∞) := (ENNReal.tsum_set_one _).symm
    _ = ∑' a, (⋃ n, B n).indicator (fun _ => (1 : ℝ≥0∞)) a :=
          tsum_subtype (⋃ n, B n) (fun _ => (1 : ℝ≥0∞))
    _ = ∑' a, ∑' n, (B n).indicator (fun _ => (1 : ℝ≥0∞)) a := by
          apply tsum_congr; intro a; exact hpoint a
    _ = ∑' n, ∑' a, (B n).indicator (fun _ => (1 : ℝ≥0∞)) a := ENNReal.tsum_comm
    _ = ∑' n, ((B n).encard : ℝ≥0∞) := by
          apply tsum_congr; intro n
          exact (tsum_subtype (B n) (fun _ => (1 : ℝ≥0∞))).symm.trans
            (ENNReal.tsum_set_one (B n))

theorem levelCount_iUnion_eq_tsum (f : ℝ → ℝ) (A : ℕ → Set ℝ)
    (h : Pairwise (Function.onFun Disjoint A)) (y : ℝ) :
    Work.Sweep.levelCount f (⋃ n, A n) y = ∑' n, Work.Sweep.levelCount f (A n) y := by
  have hB : Pairwise (Function.onFun Disjoint fun n => A n ∩ f ⁻¹' {y}) :=
    fun m n hmn => (h hmn).mono Set.inter_subset_left Set.inter_subset_left
  simp only [Work.Sweep.levelCount, Set.iUnion_inter]
  exact encard_iUnion_eq_tsum (fun n => A n ∩ f ⁻¹' {y}) hB

end Work.Sweep.LevelCountTsum
