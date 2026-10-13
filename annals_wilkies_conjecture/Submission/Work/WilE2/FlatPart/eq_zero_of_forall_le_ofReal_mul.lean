import Mathlib

namespace Work.WilE2.FlatPart

/-- If `a : ℝ≥0∞` is bounded above by `ofReal (C * ε)` for every `ε > 0`, with `C ≥ 0`,
then `a = 0`: indeed `C * ε` can be made arbitrarily small, so `a ≤ 0`. -/
theorem eq_zero_of_forall_le_ofReal_mul {a : ENNReal} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, a ≤ ENNReal.ofReal (C * ε)) : a = 0 := by
  have ha_ne_top : a ≠ ⊤ := by
    have h1 := h 1 (by norm_num)
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top)
  by_contra ha0
  have ha_pos : 0 < a := pos_iff_ne_zero.mpr ha0
  have hx : 0 < a.toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨ha_pos, lt_top_iff_ne_top.mpr ha_ne_top⟩
  have hpos : 0 < a.toReal / (2 * (C + 1)) := by positivity
  have h1 := h _ hpos
  have h2 : a.toReal ≤ (ENNReal.ofReal (C * (a.toReal / (2 * (C + 1))))).toReal :=
    (ENNReal.toReal_le_toReal ha_ne_top ENNReal.ofReal_ne_top).mpr h1
  have h3 : 0 ≤ C * (a.toReal / (2 * (C + 1))) := by positivity
  rw [ENNReal.toReal_ofReal h3] at h2
  have hden : (0 : ℝ) < 2 * (C + 1) := by linarith
  have key : C * (a.toReal / (2 * (C + 1))) < a.toReal := by
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith [hx, hC]
  linarith [h2, key]

end Work.WilE2.FlatPart
