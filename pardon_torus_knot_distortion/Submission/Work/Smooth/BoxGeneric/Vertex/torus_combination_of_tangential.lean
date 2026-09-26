import Mathlib

namespace Work.Smooth.BoxGeneric.Vertex

theorem torus_combination_of_tangential {ρ z u w0 w1 w2 : ℝ} (hρ : 0 < ρ)
    (hz : (ρ - 2) ^ 2 + z ^ 2 = 1)
    (h : (ρ - 2) * (w0 * Real.cos u + w1 * Real.sin u) + z * w2 = 0) :
    ∃ r₁ r₂ : ℝ,
      r₁ * (-(ρ * Real.sin u)) + r₂ * (-(z * Real.cos u)) = w0 ∧
      r₁ * (ρ * Real.cos u) + r₂ * (-(z * Real.sin u)) = w1 ∧
      r₂ * (ρ - 2) = w2 := by
  set c := Real.cos u with hc
  set s := Real.sin u with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc, hs]; exact Real.cos_sq_add_sin_sq u
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  by_cases hz0 : z = 0
  · have ha : (ρ - 2) ^ 2 = 1 := by simpa [hz0] using hz
    have ha_ne : ρ - 2 ≠ 0 := by intro hh; nlinarith [ha]
    have hcw : w0 * c + w1 * s = 0 := by
      have h' : (ρ - 2) * (w0 * c + w1 * s) = 0 := by simpa [hz0] using h
      exact (mul_eq_zero.mp h').resolve_left ha_ne
    have hzc : -(z * c) = 0 := by rw [hz0, zero_mul, neg_zero]
    have hzs : -(z * s) = 0 := by rw [hz0, zero_mul, neg_zero]
    refine ⟨(c * w1 - s * w0) / ρ, w2 / (ρ - 2), ?_, ?_, ?_⟩
    · rw [hzc, mul_zero, add_zero]
      field_simp
      linear_combination -c * hcw + w0 * hcs
    · rw [hzs, mul_zero, add_zero]
      field_simp
      linear_combination -s * hcw + w1 * hcs
    · field_simp
  · refine ⟨(c * w1 - s * w0) / ρ, -(w0 * c + w1 * s) / z, ?_, ?_, ?_⟩
    · field_simp
      linear_combination w0 * hcs
    · field_simp
      linear_combination w1 * hcs
    · have hz2 : (ρ - 2) * (w0 * c + w1 * s) = -(z * w2) := by linarith [h]
      field_simp
      linear_combination -hz2

end Work.Smooth.BoxGeneric.Vertex
