import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem grid_measure_shift (A : Set ℝ) (h : ℝ) (hh : 0 < h) (l : ℕ) : MeasureTheory.volume ({y : ℝ | (l : ℝ) * h + y ∈ A} ∩ Set.Ico 0 h) = MeasureTheory.volume (A ∩ Set.Ico ((l : ℝ) * h) (((l : ℝ) + 1) * h)) := by
  have hset : ({y : ℝ | (l : ℝ) * h + y ∈ A} ∩ Set.Ico 0 h)
      = (fun y : ℝ => (l : ℝ) * h + y) ⁻¹'
          (A ∩ Set.Ico ((l : ℝ) * h) (((l : ℝ) + 1) * h)) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ico]
    constructor
    · rintro ⟨hyA, hy0, hyh⟩
      exact ⟨hyA, by linarith [hh, hy0], by linarith [hh, hyh]⟩
    · rintro ⟨hyA, h1, h2⟩
      exact ⟨hyA, by linarith [hh, h1], by linarith [hh, h2]⟩
  rw [hset, MeasureTheory.measure_preimage_add]

end Work.BMF
