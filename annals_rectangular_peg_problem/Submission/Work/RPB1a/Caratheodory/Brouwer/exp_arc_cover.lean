import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

theorem exp_arc_cover (t0 t1 : ℝ) (hpos : 0 < t1) (hlt : t1 < 2 * Real.pi) (c : Circle) :
    c ∈ (fun s : ℝ => Circle.exp (t0 + t1 * (s + 1) / 2)) '' Set.Icc (-1 : ℝ) 1 ∨
      c ∈ (fun s : ℝ => Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2)) ''
        Set.Icc (-1 : ℝ) 1 := by
  -- Lift `c` to an angle `θ` and normalise it into `[t0, t0 + 2π)`.
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective c
  obtain ⟨y, hy, hyeq⟩ := Circle.periodic_exp.exists_mem_Ico Real.two_pi_pos θ t0
  have hyc : Circle.exp y = c := hyeq.symm.trans hθ
  rw [Set.mem_Ico] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rcases lt_or_ge (t0 + t1) y with hgt | hle
  · -- `y` lies on the second arc: angles `[t0 + t1, t0 + 2π]`.
    right
    refine ⟨1 - 2 * (y - t0 - t1) / (2 * Real.pi - t1), ?_, ?_⟩
    · rw [Set.mem_Icc]
      have hden : 0 < 2 * Real.pi - t1 := by linarith
      have hpos' : 0 ≤ 2 * (y - t0 - t1) / (2 * Real.pi - t1) :=
        div_nonneg (by linarith) (le_of_lt hden)
      have hle' : 2 * (y - t0 - t1) / (2 * Real.pi - t1) ≤ 2 := by
        rw [div_le_iff₀ hden]
        linarith
      constructor <;> linarith
    · have harg : t0 + t1
          + (2 * Real.pi - t1) * (1 - (1 - 2 * (y - t0 - t1) / (2 * Real.pi - t1))) / 2 = y := by
        have hden : (2 * Real.pi - t1) ≠ 0 := by linarith
        field_simp
        ring
      change Circle.exp (t0 + t1
        + (2 * Real.pi - t1) * (1 - (1 - 2 * (y - t0 - t1) / (2 * Real.pi - t1))) / 2) = c
      rw [harg, hyc]
  · -- `y` lies on the first arc: angles `[t0, t0 + t1]`.
    left
    refine ⟨2 * (y - t0) / t1 - 1, ?_, ?_⟩
    · rw [Set.mem_Icc]
      have hd : 0 ≤ 2 * (y - t0) / t1 := div_nonneg (by linarith) (le_of_lt hpos)
      have hu : 2 * (y - t0) / t1 ≤ 2 := by
        rw [div_le_iff₀ hpos]
        linarith
      constructor <;> linarith
    · have harg : t0 + t1 * ((2 * (y - t0) / t1 - 1) + 1) / 2 = y := by
        have ht1 : t1 ≠ 0 := ne_of_gt hpos
        field_simp
        ring
      change Circle.exp (t0 + t1 * ((2 * (y - t0) / t1 - 1) + 1) / 2) = c
      rw [harg, hyc]

end Work.RPB1a.Caratheodory.Brouwer
