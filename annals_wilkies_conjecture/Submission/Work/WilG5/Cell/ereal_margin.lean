import Mathlib

namespace Work.WilG5.Cell

theorem ereal_margin {a b : EReal} {t0 : ℝ} (h1 : a < (t0 : EReal)) (h2 : (t0 : EReal) < b) :
    ∃ τ : ℝ, 0 < τ ∧ a < ((t0 - τ : ℝ) : EReal) ∧ (((t0 + τ : ℝ) : EReal) < b) := by
  -- Pick real points strictly between `a` and `t0`, and between `t0` and `b`.
  obtain ⟨y, hay, hyt⟩ := EReal.exists_between_coe_real h1
  obtain ⟨z, htz, hzb⟩ := EReal.exists_between_coe_real h2
  have hyt' : y < t0 := EReal.coe_lt_coe_iff.mp hyt
  have htz' : t0 < z := EReal.coe_lt_coe_iff.mp htz
  -- Half the smaller of the two distances keeps `t0 ± τ` inside `(y, z)`.
  have hmin : 0 < min (t0 - y) (z - t0) := lt_min (sub_pos.mpr hyt') (sub_pos.mpr htz')
  refine ⟨min (t0 - y) (z - t0) / 2, ?_, ?_, ?_⟩
  · linarith
  · apply lt_of_lt_of_le hay
    apply EReal.coe_le_coe_iff.mpr
    have := min_le_left (t0 - y) (z - t0); linarith
  · apply lt_of_le_of_lt _ hzb
    apply EReal.coe_le_coe_iff.mpr
    have := min_le_right (t0 - y) (z - t0); linarith

end Work.WilG5.Cell
