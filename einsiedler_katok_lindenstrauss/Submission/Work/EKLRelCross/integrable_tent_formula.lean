import Mathlib

namespace Work.EKLRelCross

theorem integrable_tent_formula (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] (a b : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ => max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))))) μ := by
  have hcont : Continuous
      (fun t : ℝ => max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))))) := by
    fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (min a b) (max a b)) isCompact_Icc ?_
  intro t ht
  rw [Set.mem_Icc]
  rw [Function.mem_support] at ht
  have hpos : 0 < max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)))) :=
    lt_of_le_of_ne (le_max_left 0 _) (Ne.symm ht)
  have hYpos : 0 < min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))) :=
    (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
  have hZpos : 0 < min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)) :=
    lt_of_lt_of_le hYpos (min_le_right _ _)
  have h1 : 0 < (n : ℝ) * (t - a) := lt_of_lt_of_le hZpos (min_le_left _ _)
  have h2 : 0 < (n : ℝ) * (b - t) := lt_of_lt_of_le hZpos (min_le_right _ _)
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hta : 0 < t - a := (mul_pos_iff_of_pos_left hnpos).mp h1
  have hbt : 0 < b - t := (mul_pos_iff_of_pos_left hnpos).mp h2
  constructor
  · linarith [min_le_left a b]
  · linarith [le_max_right a b]

end Work.EKLRelCross
