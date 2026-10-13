import Mathlib

namespace Work.WilG4c

theorem fibreParamIoo {S : Set ℝ} {lo hi : ℝ} (hS : S = Set.Ioo lo hi) (h : lo < hi) :
    (∀ t ∈ Set.Ioo (0:ℝ) 1, lo + t * (hi - lo) ∈ S) ∧
    (∀ x ∈ S, ∃ t ∈ Set.Ioo (0:ℝ) 1, x = lo + t * (hi - lo)) := by
  have hpos : (0:ℝ) < hi - lo := sub_pos.mpr h
  constructor
  · intro t ht
    rw [hS]
    rw [Set.mem_Ioo] at ht ⊢
    obtain ⟨ht0, ht1⟩ := ht
    constructor
    · have : 0 < t * (hi - lo) := mul_pos ht0 hpos
      linarith
    · have : t * (hi - lo) < 1 * (hi - lo) := mul_lt_mul_of_pos_right ht1 hpos
      linarith
  · intro x hx
    rw [hS] at hx
    rw [Set.mem_Ioo] at hx
    obtain ⟨hx0, hx1⟩ := hx
    refine ⟨(x - lo) / (hi - lo), ?_, ?_⟩
    · rw [Set.mem_Ioo]
      refine ⟨div_pos (by linarith) hpos, ?_⟩
      rw [div_lt_one hpos]
      linarith
    · have hne : hi - lo ≠ 0 := ne_of_gt hpos
      field_simp
      ring

end Work.WilG4c
