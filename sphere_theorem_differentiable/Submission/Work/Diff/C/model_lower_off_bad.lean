import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open Real

theorem model_lower_off_bad
    {β : ℝ} (hβ : -1 ≤ β) {α c σ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ Real.pi / 4) (hc : 0 < c)
    (hnum : 3 * c ≤ 1 - Real.cos α) (hσ0 : 0 ≤ σ) (hσπ : σ ≤ Real.pi)
    (hbad : ¬ (σ ∈ Set.Icc (Real.pi / 2 - α) (Real.pi / 2 + α) ∧ β ≤ -Real.cos α)) :
    -1 + 3 * c ≤ β * Real.sin σ := by
  have hpi := Real.pi_pos
  have hcospos : 0 < Real.cos α := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hcosle : -1 + 3 * c ≤ -Real.cos α := by linarith
  have hsinσ : 0 ≤ Real.sin σ := Real.sin_nonneg_of_nonneg_of_le_pi hσ0 hσπ
  have hkey : -Real.cos α ≤ β * Real.sin σ := by
    rcases not_and_or.mp hbad with hnot | hb
    · -- σ ∉ Icc
      have hcases : σ < Real.pi / 2 - α ∨ Real.pi / 2 + α < σ := by
        have h := hnot
        simp only [Set.mem_Icc, not_and_or, not_le] at h
        exact h
      have hsin_le : Real.sin σ ≤ Real.cos α := by
        rcases hcases with h | h
        · have h1 : -(Real.pi / 2) ≤ σ := by linarith
          have h2 : Real.pi / 2 - α ≤ Real.pi / 2 := by linarith
          have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 (le_of_lt h)
          simpa [Real.sin_pi_div_two_sub] using h3
        · have hle : Real.pi - σ ≤ Real.pi / 2 - α := by linarith
          have h1 : -(Real.pi / 2) ≤ Real.pi - σ := by linarith
          have h2 : Real.pi / 2 - α ≤ Real.pi / 2 := by linarith
          have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 hle
          rw [Real.sin_pi_sub, Real.sin_pi_div_two_sub] at h3
          exact h3
      have hb1 : -Real.sin σ ≤ β * Real.sin σ := by
        have : 0 ≤ (β + 1) * Real.sin σ := mul_nonneg (by linarith) hsinσ
        nlinarith [this]
      linarith
    · -- β > -cos α
      have hgt : -Real.cos α < β := lt_of_not_ge hb
      have h1 : (-Real.cos α) * Real.sin σ ≤ β * Real.sin σ :=
        mul_le_mul_of_nonneg_right (le_of_lt hgt) hsinσ
      have h2 : -Real.cos α ≤ (-Real.cos α) * Real.sin σ := by
        have hle : Real.cos α * Real.sin σ ≤ Real.cos α := by
          nlinarith [hcospos, Real.sin_le_one σ]
        linarith
      linarith
  linarith

end Work.Diff.C
