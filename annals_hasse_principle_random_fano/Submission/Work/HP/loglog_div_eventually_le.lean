import Mathlib

namespace Work.HP

theorem loglog_div_eventually_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ B in Filter.atTop, C * Real.log B / Real.log (Real.log B) ≤ ε * Real.log B := by
  have hloglog : Filter.Tendsto (fun B : ℝ => Real.log (Real.log B)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hM := hloglog.eventually_ge_atTop (max (C / ε) 1)
  have hlogB : ∀ᶠ B in Filter.atTop, (1 : ℝ) < Real.log B :=
    Real.tendsto_log_atTop.eventually_gt_atTop 1
  filter_upwards [hM, hlogB] with B hM hlogB
  have hlogLpos : 0 < Real.log (Real.log B) :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hM)
  have hLpos : 0 < Real.log B := lt_trans one_pos hlogB
  have hCε : C / ε ≤ Real.log (Real.log B) := le_trans (le_max_left _ _) hM
  have hCle : C ≤ ε * Real.log (Real.log B) := by
    have h1 : ε * (C / ε) = C := by rw [mul_comm, div_mul_cancel₀ C (ne_of_gt hε)]
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hCε (le_of_lt hε)
  rw [div_le_iff₀ hlogLpos]
  have h2 : C * Real.log B ≤ (ε * Real.log (Real.log B)) * Real.log B :=
    mul_le_mul_of_nonneg_right hCle (le_of_lt hLpos)
  nlinarith [h2]

end Work.HP
