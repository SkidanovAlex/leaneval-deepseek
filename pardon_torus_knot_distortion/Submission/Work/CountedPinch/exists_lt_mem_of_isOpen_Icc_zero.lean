import Mathlib

namespace Work.CountedPinch

open Metric

/-- **An open subset of `[0,1]` containing the left endpoint contains a one-sided interval.**
There is `ε > 0`, `ε ≤ 1`, such that every `t ∈ [0,1]` with `t < ε` belongs to `A`. -/
theorem exists_lt_mem_of_isOpen_Icc_zero {A : Set (Set.Icc (0 : ℝ) 1)} (hA : IsOpen A)
    (h0 : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ A) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1), t < ε →
      (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1) ∈ A := by
  rw [Metric.isOpen_iff] at hA
  obtain ⟨ε, hε, hsub⟩ := hA _ h0
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, ?_⟩
  intro t ht htlt
  apply hsub
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  exact lt_of_lt_of_le htlt (min_le_left _ _)

end Work.CountedPinch
