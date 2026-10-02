import Submission.Work.Stems.Hur2.ConeQuot

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The radius of the cone map

`bd t` always lies on the boundary `∂I²`, hence has max-norm radius `rad (bd t) = 1`; the cone map
scales that radius linearly, so `rad (coneMap (s,t)) = 1 - s`.  This invariant separates the two
parameters `s`, `t` in the fibres of `coneMap`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

theorem bd1_eq_zero_of_le_quarter (t : unitInterval) (h : (t : ℝ) ≤ 1 / 4) : bd1 t = 0 := by
  unfold bd1
  rw [max_def, min_def, min_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

theorem bd0_eq_one_of_quarter_le (t : unitInterval) (h : 1 / 4 ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ 1 / 2) :
    bd0 t = 1 := by
  unfold bd0
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

theorem bd1_eq_one_of_half_le (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ 3 / 4) :
    bd1 t = 1 := by
  unfold bd1
  rw [max_def, min_def, min_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

theorem bd0_eq_zero_of_three_quarter_le (t : unitInterval) (h : 3 / 4 ≤ (t : ℝ)) : bd0 t = 0 := by
  unfold bd0
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

/-- On the first quarter the first coordinate is linear. -/
theorem bd0_eq_of_le_quarter (t : unitInterval) (h : (t : ℝ) ≤ 1 / 4) :
    (bd0 t : ℝ) = 4 * (t : ℝ) := by
  unfold bd0
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

/-- On the second quarter the second coordinate is linear. -/
theorem bd1_eq_of_quarter_le (t : unitInterval) (h : 1 / 4 ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ 1 / 2) : (bd1 t : ℝ) = 4 * (t : ℝ) - 1 := by
  unfold bd1
  rw [max_def, min_def, min_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

/-- On the third quarter the first coordinate is linear. -/
theorem bd0_eq_of_half_le (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ 3 / 4) : (bd0 t : ℝ) = 3 - 4 * (t : ℝ) := by
  unfold bd0
  rw [min_def, min_def, max_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

/-- On the fourth quarter the second coordinate is linear. -/
theorem bd1_eq_of_three_quarter_le (t : unitInterval) (h : 3 / 4 ≤ (t : ℝ)) :
    (bd1 t : ℝ) = 4 - 4 * (t : ℝ) := by
  unfold bd1
  rw [max_def, min_def, min_def]
  split_ifs <;> linarith [t.2.1, t.2.2]

theorem bd_apply_one_eq_zero_of_le_quarter (t : unitInterval) (h : (t : ℝ) ≤ 1 / 4) :
    (bd t : IC 2) 1 = 0 := by
  rw [bd_apply_one]
  exact Subtype.ext (bd1_eq_zero_of_le_quarter t h)

theorem bd_apply_zero_eq_one_of_quarter_le (t : unitInterval) (h : 1 / 4 ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ 1 / 2) : (bd t : IC 2) 0 = 1 := by
  rw [bd_apply_zero]
  exact Subtype.ext (bd0_eq_one_of_quarter_le t h h2)

theorem bd_apply_one_eq_one_of_half_le (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ 3 / 4) : (bd t : IC 2) 1 = 1 := by
  rw [bd_apply_one]
  exact Subtype.ext (bd1_eq_one_of_half_le t h h2)

theorem bd_apply_zero_eq_zero_of_three_quarter_le (t : unitInterval) (h : 3 / 4 ≤ (t : ℝ)) :
    (bd t : IC 2) 0 = 0 := by
  rw [bd_apply_zero]
  exact Subtype.ext (bd0_eq_zero_of_three_quarter_le t h)

/-- Every point of the parametrised boundary lies on `∂I²`. -/
theorem bd_mem_boundary (t : unitInterval) : bd t ∈ Cube.boundary (Fin 2) := by
  rw [Cube.boundary]
  by_cases h1 : (t : ℝ) ≤ 1 / 4
  · exact ⟨1, Or.inl (bd_apply_one_eq_zero_of_le_quarter t h1)⟩
  · have h1' : 1 / 4 ≤ (t : ℝ) := le_of_lt (not_le.mp h1)
    by_cases h2 : (t : ℝ) ≤ 1 / 2
    · exact ⟨0, Or.inr (bd_apply_zero_eq_one_of_quarter_le t h1' h2)⟩
    · have h2' : 1 / 2 ≤ (t : ℝ) := le_of_lt (not_le.mp h2)
      by_cases h3 : (t : ℝ) ≤ 3 / 4
      · exact ⟨1, Or.inr (bd_apply_one_eq_one_of_half_le t h2' h3)⟩
      · exact ⟨0, Or.inl (bd_apply_zero_eq_zero_of_three_quarter_le t
          (le_of_lt (not_le.mp h3)))⟩

/-- The max-norm radius of a boundary point of the parametrised boundary is `1`. -/
theorem rad_bd (t : unitInterval) : rad (bd t) = 1 := by
  refine le_antisymm (rad_le_one (bd t)) ?_
  rw [rad_eq_max]
  by_cases h1 : (t : ℝ) ≤ 1 / 4
  · have hz : |2 * ((bd t : IC 2) 1 : ℝ) - 1| = 1 := by
      rw [bd_apply_one_eq_zero_of_le_quarter t h1]
      norm_num
    rw [hz]; exact le_max_right _ _
  · have h1' : 1 / 4 ≤ (t : ℝ) := le_of_lt (not_le.mp h1)
    by_cases h2 : (t : ℝ) ≤ 1 / 2
    · have hz : |2 * ((bd t : IC 2) 0 : ℝ) - 1| = 1 := by
        rw [bd_apply_zero_eq_one_of_quarter_le t h1' h2]
        norm_num
      rw [hz]; exact le_max_left _ _
    · have h2' : 1 / 2 ≤ (t : ℝ) := le_of_lt (not_le.mp h2)
      by_cases h3 : (t : ℝ) ≤ 3 / 4
      · have hz : |2 * ((bd t : IC 2) 1 : ℝ) - 1| = 1 := by
          rw [bd_apply_one_eq_one_of_half_le t h2' h3]
          norm_num
        rw [hz]; exact le_max_right _ _
      · have hz : |2 * ((bd t : IC 2) 0 : ℝ) - 1| = 1 := by
          rw [bd_apply_zero_eq_zero_of_three_quarter_le t (le_of_lt (not_le.mp h3))]
          norm_num
        rw [hz]; exact le_max_left _ _

/-- The cone map scales the radius linearly: `rad (coneMap (s,t)) = 1 - s`. -/
theorem rad_coneMap (s t : IC 1) : rad (coneMap (s, t)) = 1 - (s 0 : ℝ) := by
  have hs : 0 ≤ 1 - (s 0 : ℝ) := by linarith [(s 0).2.2]
  have hcoord : ∀ j : Fin 2,
      |2 * ((coneMap (s, t) : IC 2) j : ℝ) - 1|
        = (1 - (s 0 : ℝ)) * |2 * ((bd (t 0) : IC 2) j : ℝ) - 1| := by
    intro j
    have hval : ((coneMap (s, t) : IC 2) j : ℝ)
        = 1 / 2 + (1 - (s 0 : ℝ)) * (((bd (t 0) : IC 2) j : ℝ) - 1 / 2) := rfl
    have key : 2 * (1 / 2 + (1 - (s 0 : ℝ)) * (((bd (t 0) : IC 2) j : ℝ) - 1 / 2)) - 1
        = (1 - (s 0 : ℝ)) * (2 * ((bd (t 0) : IC 2) j : ℝ) - 1) := by ring
    rw [hval, key, abs_mul, abs_of_nonneg hs]
  have hmax : max |2 * ((bd (t 0) : IC 2) 0 : ℝ) - 1|
      |2 * ((bd (t 0) : IC 2) 1 : ℝ) - 1| = 1 := by
    rw [← rad_eq_max]; exact rad_bd (t 0)
  rw [rad_eq_max, hcoord 0, hcoord 1]
  rcases le_total |2 * ((bd (t 0) : IC 2) 0 : ℝ) - 1|
    |2 * ((bd (t 0) : IC 2) 1 : ℝ) - 1| with h | h
  · rw [max_eq_right h] at hmax
    rw [max_eq_right (mul_le_mul_of_nonneg_left h hs), hmax, mul_one]
  · rw [max_eq_left h] at hmax
    rw [max_eq_left (mul_le_mul_of_nonneg_left h hs), hmax, mul_one]

end

end Work.Stems.Hur2
