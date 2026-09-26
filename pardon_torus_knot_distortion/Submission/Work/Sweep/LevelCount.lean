import Mathlib
import ChallengeDeps

/-!
# Counting the level sets of a function

This file sets up the general notion used by the one-dimensional coarea formula:
`levelCount f s y` is the number of points of `s` at which `f` takes the value
`y`, as an extended nonnegative real (`⊤` if there are infinitely many).

The main structural facts are that `levelCount` is additive over disjoint unions
and that for an injective function it is the indicator function of the image.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Function

namespace Work.Sweep

/-- The number of points of `s` at which `f` takes the value `y`, as an extended
nonnegative real (`⊤` when there are infinitely many). -/
def levelCount (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) : ℝ≥0∞ :=
  ↑((s ∩ f ⁻¹' {y}).encard)

@[simp]
lemma levelCount_empty (f : ℝ → ℝ) (y : ℝ) : levelCount f ∅ y = 0 := by
  simp [levelCount]

lemma levelCount_mono {f : ℝ → ℝ} {s t : Set ℝ} (h : s ⊆ t) (y : ℝ) :
    levelCount f s y ≤ levelCount f t y := by
  have h' : s ∩ f ⁻¹' {y} ⊆ t ∩ f ⁻¹' {y} := fun z hz => ⟨h hz.1, hz.2⟩
  rw [levelCount, levelCount, ENat.toENNReal_le]
  exact Set.encard_le_encard h'

lemma levelCount_mono_set {f : ℝ → ℝ} {s t : Set ℝ} (h : s ⊆ t) :
    levelCount f s ≤ levelCount f t := fun y => levelCount_mono h y

/-- The level count of a set is zero exactly at the levels that are not attained. -/
lemma levelCount_eq_zero_iff {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} :
    levelCount f s y = 0 ↔ Disjoint s (f ⁻¹' {y}) := by
  rw [levelCount, ENat.toENNReal_eq_zero, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro x hx hxy
    exact h x ⟨hx, hxy⟩
  · intro h
    rintro x ⟨hx, hxy⟩
    exact Set.disjoint_left.mp h hx hxy

lemma levelCount_pos_iff {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} :
    0 < levelCount f s y ↔ (s ∩ f ⁻¹' {y}).Nonempty := by
  rw [levelCount, ← ENat.toENNReal_zero, ENat.toENNReal_lt, Set.encard_pos]

/-- The level count is the extended cardinality of the intersection. -/
lemma levelCount_eq_encard (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) :
    levelCount f s y = ↑((s ∩ f ⁻¹' {y}).encard) := rfl

lemma levelCount_ne_top_iff {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} :
    levelCount f s y ≠ ⊤ ↔ (s ∩ f ⁻¹' {y}).Finite := by
  rw [levelCount, ENat.toENNReal_ne_top, Set.encard_ne_top_iff]

lemma levelCount_lt_top_iff {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} :
    levelCount f s y < ⊤ ↔ (s ∩ f ⁻¹' {y}).Finite := by
  rw [levelCount, ENat.toENNReal_lt_top, Set.encard_lt_top_iff]

/-- Level counts of disjoint sets add. -/
lemma levelCount_union {f : ℝ → ℝ} {s t : Set ℝ} (h : Disjoint s t) (y : ℝ) :
    levelCount f (s ∪ t) y = levelCount f s y + levelCount f t y := by
  have hd : Disjoint (s ∩ f ⁻¹' {y}) (t ∩ f ⁻¹' {y}) :=
    h.mono Set.inter_subset_left Set.inter_subset_left
  rw [levelCount, levelCount, levelCount, Set.union_inter_distrib_right,
    Set.encard_union_eq hd, ENat.toENNReal_add]

/-- Additivity of the level count over the partial unions of a pairwise disjoint
sequence of sets. -/
lemma levelCount_iUnion_range {f : ℝ → ℝ} {s : ℕ → Set ℝ} (h : Pairwise (Disjoint on s))
    (n : ℕ) (y : ℝ) :
    levelCount f (⋃ i ∈ Finset.range n, s i) y = ∑ i ∈ Finset.range n, levelCount f (s i) y := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdisj : Disjoint (⋃ i ∈ Finset.range n, s i) (s n) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        rw [Set.mem_iUnion₂] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        exact Set.disjoint_left.mp (@h i n (Finset.mem_range.mp hi).ne) hxi hx'
      have hunion : (⋃ i ∈ Finset.range (n + 1), s i) = (⋃ i ∈ Finset.range n, s i) ∪ s n := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_range]
        constructor
        · rintro ⟨i, hi, hx⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
          · exact Or.inl ⟨i, hlt, hx⟩
          · exact Or.inr (heq ▸ hx)
        · rintro (⟨i, hi, hx⟩ | hx)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
          · exact ⟨n, Nat.lt_succ_self n, hx⟩
      rw [hunion, levelCount_union (f := f) (s := ⋃ i ∈ Finset.range n, s i) (t := s n) hdisj,
        ih, Finset.sum_range_succ]

/-- For an injective function the level count is the indicator of the image: every
attained level has exactly one preimage. -/
lemma levelCount_eq_indicator_of_injOn {f : ℝ → ℝ} {s : Set ℝ} (h : InjOn f s) :
    levelCount f s = Set.indicator (f '' s) (fun _ => (1 : ℝ≥0∞)) := by
  funext y
  by_cases hy : y ∈ f '' s
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [Set.indicator_of_mem (Set.mem_image_of_mem f hx)]
    have hsingle : s ∩ f ⁻¹' {f x} = {x} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => h hz.1 hx hz.2, fun hz => ⟨by rw [hz]; exact hx, by rw [hz]⟩⟩
    rw [levelCount, hsingle, Set.encard_singleton, ENat.toENNReal_one]
  · rw [Set.indicator_of_notMem hy]
    rw [levelCount_eq_zero_iff]
    rw [Set.disjoint_left]
    rintro x hx hxy
    exact hy ⟨x, hx, hxy⟩

lemma levelCount_eq_indicator_of_injOn_apply {f : ℝ → ℝ} {s : Set ℝ} (h : InjOn f s) (y : ℝ) :
    levelCount f s y = (f '' s).indicator (fun _ => (1 : ℝ≥0∞)) y :=
  congrFun (levelCount_eq_indicator_of_injOn h) y

/-- If the level set is finite then the level count is the honest `ncard`. -/
lemma levelCount_eq_ncard {f : ℝ → ℝ} {s : Set ℝ} (y : ℝ)
    (h : (s ∩ f ⁻¹' {y}).Finite) : levelCount f s y = ((s ∩ f ⁻¹' {y}).ncard : ℝ≥0∞) := by
  rw [levelCount, h.encard_eq_coe_toFinset_card, ENat.toENNReal_coe, Set.ncard_eq_toFinset_card _ h]

/-- The level count of a level that is attained is at least one. -/
lemma one_le_levelCount {f : ℝ → ℝ} {s : Set ℝ} {y : ℝ} (h : (s ∩ f ⁻¹' {y}).Nonempty) :
    1 ≤ levelCount f s y := by
  rw [levelCount, ← ENat.toENNReal_one, ENat.toENNReal_le]
  rw [Set.one_le_encard_iff_nonempty]
  exact h

@[simp]
lemma levelCount_univ (f : ℝ → ℝ) (y : ℝ) : levelCount f univ y = ↑((f ⁻¹' {y}).encard) := by
  rw [levelCount, Set.univ_inter]

end Work.Sweep
