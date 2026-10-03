import Mathlib
import Submission.Work.FITop3.Smooth

namespace Work.FITop3.Smooth

/-- The clamp ramp `sm` is strictly positive on `(0, ∞)`. -/
theorem sm_pos_of_pos (t : ℝ) (ht : 0 < t) : 0 < Work.FITop3.sm t := by
  unfold Work.FITop3.sm
  split_ifs with h1 h2 h3
  · exact absurd h1 (not_le.mpr ht)
  · nlinarith [sq_pos_of_pos ht]
  · nlinarith [sq_nonneg (1 - t), h2, h3]
  · norm_num

/-- The clamp ramp `sm` is strictly less than `1` on `(-∞, 1)`. -/
theorem sm_lt_one_of_lt_one (t : ℝ) (ht : t < 1) : Work.FITop3.sm t < 1 := by
  unfold Work.FITop3.sm
  split_ifs with h1 h2 h3
  · norm_num
  · nlinarith [sq_nonneg t, sq_nonneg (t - 1 / 2)]
  · nlinarith [sq_nonneg (1 - t), h2, h3]
  · exact absurd (le_of_lt ht) h3

set_option maxHeartbeats 1000000 in
theorem sm_props :
    (∀ t : ℝ, 0 ≤ Work.FITop3.sm t) ∧ (∀ t : ℝ, Work.FITop3.sm t ≤ 1) ∧
    (∀ t : ℝ, Work.FITop3.sm t = 0 ↔ t ≤ 0) ∧ (∀ t : ℝ, Work.FITop3.sm t = 1 ↔ 1 ≤ t) ∧
    (∀ t δ : ℝ, 0 ≤ δ → |Work.FITop3.sm (t + δ) - Work.FITop3.sm t| ≤ 2 * δ + 2 * δ ^ 2) ∧
    (∀ t δ : ℝ, 0 ≤ δ → |Work.FITop3.sm (t + 2 * δ) - 2 * Work.FITop3.sm (t + δ) + Work.FITop3.sm t|
      ≤ 4 * δ ^ 2 + 8 * δ ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    unfold Work.FITop3.sm
    split_ifs with h1 h2 h3
    · norm_num
    · nlinarith [sq_nonneg t]
    · nlinarith [sq_nonneg (1 - t), h2, h3]
    · norm_num
  · intro t
    unfold Work.FITop3.sm
    split_ifs with h1 h2 h3
    · norm_num
    · nlinarith [sq_nonneg t]
    · nlinarith [sq_nonneg (1 - t), h2, h3]
    · norm_num
  · intro t
    constructor
    · intro h
      by_contra ht
      have hp : 0 < Work.FITop3.sm t := sm_pos_of_pos t (not_le.mp ht)
      rw [h] at hp
      exact absurd hp (lt_irrefl 0)
    · intro ht
      unfold Work.FITop3.sm
      simp only [if_pos ht]
  · intro t
    constructor
    · intro h
      by_contra ht
      have hl : Work.FITop3.sm t < 1 := sm_lt_one_of_lt_one t (not_le.mp ht)
      rw [h] at hl
      exact absurd hl (lt_irrefl 1)
    · intro ht
      have h0 : ¬ t ≤ 0 := not_le.mpr (lt_of_lt_of_le (by norm_num) ht)
      have h2 : ¬ t ≤ 1 / 2 := not_le.mpr (lt_of_lt_of_le (by norm_num) ht)
      unfold Work.FITop3.sm
      rw [if_neg h0, if_neg h2]
      by_cases h3 : t ≤ 1
      · rw [if_pos h3]
        have h1 : t = 1 := le_antisymm h3 ht
        rw [h1]; norm_num
      · rw [if_neg h3]
  · intro t δ hδ
    unfold Work.FITop3.sm
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals (try (rw [abs_le]; constructor <;> nlinarith [hδ, sq_nonneg δ]))
  · intro t δ hδ
    unfold Work.FITop3.sm
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
    all_goals (try (rw [abs_le]; constructor <;> nlinarith [hδ, sq_nonneg δ]))

end Work.FITop3.Smooth
