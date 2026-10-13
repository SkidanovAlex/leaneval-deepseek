import Mathlib

namespace Work.WilE5.Cells

/-- For a finite family of real numbers, there is a positive `ε` strictly below
every nonzero absolute value `|r i|`: take half the minimum of the nonzero
values. -/
theorem khovEps {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, r i ≠ 0 → ε < |r i| := by
  classical
  by_cases h : ∃ i, r i ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h
    obtain ⟨i₁, hi₁, hmin⟩ :=
      Finset.exists_min_image (Finset.univ.filter (fun i => r i ≠ 0)) (fun i => |r i|)
        ⟨i₀, by simp [hi₀]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁
    refine ⟨|r i₁| / 2, by linarith [abs_pos.mpr hi₁], fun i hi => ?_⟩
    have hle : |r i₁| ≤ |r i| := hmin i (by simp [hi])
    linarith [abs_pos.mpr hi₁]
  · push Not at h
    exact ⟨1, one_pos, fun i hi => absurd (h i) hi⟩

end Work.WilE5.Cells
