import Mathlib

namespace Work.CNum.GridCover

/-- The 1024 intervals `[k/1024, (k+1)/1024]`, `k < 1024`, cover `[0,1]`. -/
lemma grid_cover (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 1024 ∧ t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024) := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rcases le_or_gt (t * 1024) (1023 : ℝ) with hle | hlt
  · -- `t ≤ 1023/1024`: take `m = ⌊1024 t⌋`, which is `< 1024`.
    set m : ℕ := ⌊1024 * t⌋₊
    have h1 : (m : ℝ) ≤ 1024 * t := Nat.floor_le (by positivity)
    have h2 : 1024 * t < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm_lt : m < 1024 := by
      have hc : (m : ℝ) ≤ 1023 := by linarith
      exact_mod_cast lt_of_le_of_lt hc (by norm_num : (1023 : ℝ) < 1024)
    refine ⟨m, hm_lt, ?_, ?_⟩
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)]
      linarith
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)]
      linarith
  · -- `1023/1024 < t ≤ 1`: take `k = 1023`.
    refine ⟨1023, by norm_num, ?_, ?_⟩
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)]
      push_cast
      linarith
    · have h : (((1023 : ℕ) : ℝ) + 1) / 1024 = 1 := by norm_num
      rw [h]
      exact ht1

end Work.CNum.GridCover
