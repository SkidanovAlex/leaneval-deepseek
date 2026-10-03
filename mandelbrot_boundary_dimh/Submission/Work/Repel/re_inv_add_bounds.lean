import Mathlib

namespace Work.Repel

theorem re_inv_add_bounds (a₂ : ℕ) (β : ℂ) (ha₂ : 4 ≤ a₂) (hβre : 0 ≤ β.re) (hβre' : β.re < 1) :
    (1 / ((a₂ : ℂ) + β)).re ≤ 1 / 2 ∧ -(1 / 2) < (1 / ((a₂ : ℂ) + β)).re := by
  set z : ℂ := (a₂ : ℂ) + β with hz
  -- real part of z is at least 4
  have hzre : z.re = (a₂ : ℝ) + β.re := by
    rw [hz]; simp
  have h4 : (4:ℝ) ≤ z.re := by
    have : (4:ℝ) ≤ (a₂:ℝ) := by exact_mod_cast ha₂
    linarith
  have hzre_pos : 0 < z.re := by linarith
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hzre_pos; simp at hzre_pos
  have hnsq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hzne
  -- normSq z ≥ 2 * z.re since z.re ≥ 4 > 2
  have htwo : 2 * z.re ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im, h4]
  -- 1/z has real part z.re / normSq z
  have hinv : (1 / z).re = z.re / Complex.normSq z := by
    simp only [one_div]
    exact Complex.inv_re z
  rw [hinv]
  constructor
  · rw [div_le_iff₀ hnsq_pos]
    linarith
  · have : 0 < z.re / Complex.normSq z := div_pos hzre_pos hnsq_pos
    linarith

end Work.Repel
