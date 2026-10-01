import Mathlib

namespace Work.LinnikBurgess

/-!
# The `a2` distance count

Counting lemma used for the `a2`-sum: for a pivot `x ∈ [1,H]`, the sum over
`y ∈ [1,H]`, `y ≠ x`, of a weight depending only on `|x - y|` is at most twice
the sum of the same weight over `c ∈ [1, H-1]`.  The point is that the map
`y ↦ |x - y|` is at most two-to-one; equivalently the terms with `y < x` and
those with `y > x` each reproduce, after the change of variable
`y ↦ |x - y|`, a sum over a sub-interval of `[1, H-1]`.

The proof splits the range at the pivot:

* `y < x` gives `|x - y| = x - y`, running bijectively over `[1, x-1]`;
* `y > x` gives `|x - y| = y - x`, running bijectively over `[1, H-x]`.

Both intervals are contained in `[1, H-1]`, and `F ≥ 0` makes the sums
monotone under inclusion.
-/

/-- For `b ≤ a`, the integer difference `a - b` is the natural number `a - b`. -/
lemma a2_natAbs_cast_sub_of_le {a b : ℕ} (h : b ≤ a) : (((a : ℤ) - (b : ℤ)).natAbs) = a - b := by
  rw [← Nat.cast_sub h, Int.natAbs_natCast]

/-- For `a ≤ b`, the absolute value of the integer difference `a - b` is `b - a`. -/
lemma a2_natAbs_cast_sub_of_le' {a b : ℕ} (h : a ≤ b) : (((a : ℤ) - (b : ℤ)).natAbs) = b - a := by
  have h1 : (a : ℤ) - (b : ℤ) = -↑(b - a) := by rw [Nat.cast_sub h]; ring
  rw [h1, Int.natAbs_neg, Int.natAbs_natCast]

/-- The part of the `a2`-sum with `y < x` reindexes onto `[1, x-1]`. -/
lemma a2_sum_filter_lt (F : ℕ → ℝ) {H x : ℕ} (hxH : x ≤ H) :
    (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y < x), F (((x : ℤ) - (y : ℤ)).natAbs))
      = ∑ c ∈ Finset.Icc 1 (x - 1), F c := by
  refine Finset.sum_bij' (fun y _ => x - y) (fun c _ => x - c) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
    obtain ⟨hc1, hcx⟩ := hc
    omega
  · intro y hy
    show x - (x - y) = y
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    omega
  · intro c hc
    show x - (x - c) = c
    simp only [Finset.mem_Icc] at hc
    omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    congr 1
    exact a2_natAbs_cast_sub_of_le (by omega)

/-- The part of the `a2`-sum with `x < y` reindexes onto `[1, H-x]`. -/
lemma a2_sum_filter_gt (F : ℕ → ℝ) {H x : ℕ} (hxH : x ≤ H) :
    (∑ y ∈ (Finset.Icc 1 H).filter (fun y => x < y), F (((x : ℤ) - (y : ℤ)).natAbs))
      = ∑ c ∈ Finset.Icc 1 (H - x), F c := by
  refine Finset.sum_bij' (fun y _ => y - x) (fun c _ => x + c) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
    obtain ⟨hc1, hcx⟩ := hc
    omega
  · intro y hy
    show x + (y - x) = y
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    omega
  · intro c hc
    show x + c - x = c
    omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hyH⟩, hyx⟩ := hy
    congr 1
    exact a2_natAbs_cast_sub_of_le' (by omega)

/-- For `1 ≤ x ≤ H` and a nonnegative weight `F`, the sum of `F (|x-y|)` over
`y ∈ [1,H]`, `y ≠ x`, is at most `2 * ∑_{c ∈ [1,H-1]} F c`. -/
theorem a2_dist_le_two_Icc {H x : ℕ} (hx1 : 1 ≤ x) (hxH : x ≤ H) {F : ℕ → ℝ}
    (hF : ∀ n, 0 ≤ F n) :
    (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x), F (((x : ℤ) - (y : ℤ)).natAbs))
      ≤ 2 * ∑ c ∈ Finset.Icc 1 (H - 1), F c := by
  have hdisj : Disjoint ((Finset.Icc 1 H).filter (fun y => y < x))
      ((Finset.Icc 1 H).filter (fun y => x < y)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_filter] at hy1 hy2
    omega
  have hset : (Finset.Icc 1 H).filter (fun y => y ≠ x)
      = (Finset.Icc 1 H).filter (fun y => y < x) ∪ (Finset.Icc 1 H).filter (fun y => x < y) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_union hdisj, a2_sum_filter_lt F hxH, a2_sum_filter_gt F hxH]
  have h1 : (∑ c ∈ Finset.Icc 1 (x - 1), F c) ≤ ∑ c ∈ Finset.Icc 1 (H - 1), F c :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro c hc; simp only [Finset.mem_Icc] at hc ⊢; omega)
      (by intro i _ _; exact hF i)
  have h2 : (∑ c ∈ Finset.Icc 1 (H - x), F c) ≤ ∑ c ∈ Finset.Icc 1 (H - 1), F c :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro c hc; simp only [Finset.mem_Icc] at hc ⊢; omega)
      (by intro i _ _; exact hF i)
  linarith

end Work.LinnikBurgess
