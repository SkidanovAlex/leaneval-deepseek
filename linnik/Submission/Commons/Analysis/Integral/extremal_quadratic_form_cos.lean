import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Integral

/-- Algebraic core: an identity in `s, c, θ, k` under the two relations
`s² + c² = 1` and `s² = k (1 - θ c/s)`.  Clearing denominators and using the
second relation to replace `k` turns the claim into a polynomial identity. -/
theorem extremal_quadratic_form_cos_aux {θ s c k : ℝ}
    (hsc : s ^ 2 + c ^ 2 = 1) (hc : c ≠ 0) (hs : s ≠ 0)
    (hcon : s ^ 2 = k * (1 - θ * (c / s))) :
    2 * (s / c) ^ 2 + 3 - 3 * θ * (s / c) - 3 * θ * (c / s)
      - k * (2 * (1 + (s / c) ^ 2) * (1 - θ * (c / s)) ^ 2)
    = - (1 + (s / c) ^ 2) * c ^ 2
        * (θ * (s / c) + 3 * θ * (c / s) - 3) := by
  have hA : 1 - θ * (c / s) = (s - θ * c) / s := by field_simp
  have hkne : s - θ * c ≠ 0 := by
    intro hzero
    have hA0 : 1 - θ * (c / s) = 0 := by rw [hA, hzero]; ring
    rw [hA0, mul_zero] at hcon
    exact hs (sq_eq_zero_iff.mp hcon)
  have hk1 : s ^ 3 = k * (s - θ * c) := by
    rw [hA] at hcon
    field_simp [hs] at hcon
    linarith [hcon]
  have hk : k = s ^ 3 / (s - θ * c) := by
    rw [eq_div_iff hkne]
    exact hk1.symm
  have h1 : 1 + (s / c) ^ 2 = 1 / c ^ 2 := by
    field_simp
    linarith [hsc]
  rw [hA, hk, h1]
  field_simp
  ring

theorem extremal_quadratic_form_cos {θ k : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hk0 : 0 < k) (hk3 : k < 3)
    (hcon : Real.sin θ ^ 2 = k * (1 - θ * (Real.cos θ / Real.sin θ))) :
    2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ)
      - k * (2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.cos θ / Real.sin θ)) ^ 2)
    = - (1 + Real.tan θ ^ 2) * Real.cos θ ^ 2
        * (θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) - 3) := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩
  have hspos : 0 < Real.sin θ :=
    Real.sin_pos_of_mem_Ioo ⟨hθ0, by linarith [Real.pi_pos, hθ1]⟩
  rw [Real.tan_eq_sin_div_cos]
  exact extremal_quadratic_form_cos_aux (Real.sin_sq_add_cos_sq θ)
    (ne_of_gt hcpos) (ne_of_gt hspos) hcon

end Commons.Analysis.Integral