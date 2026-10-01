import Mathlib

namespace Work.LinnikAreas.Density4

/-- If `θ ∈ (0, π)` and `|z| < θ`, then `cos θ < cos z`. -/
lemma cos_theta_lt_cos_of_abs_lt (θ z : ℝ) (hθπ : θ < Real.pi) (hz : |z| < θ) :
    Real.cos θ < Real.cos z := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg z) hθπ.le hz
  rwa [Real.cos_abs] at h

theorem cos_diff_prod_integral_pos (θ s : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hs0 : 0 < s) (hs2 : s < 2 * θ) :
    0 < ∫ v in (s - θ)..θ,
          (Real.cos v - Real.cos θ) * (Real.cos (s - v) - Real.cos θ) := by
  have hab : s - θ < θ := by linarith
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hab
  · exact (by fun_prop : Continuous
        (fun v => (Real.cos v - Real.cos θ) * (Real.cos (s - v) - Real.cos θ))).intervalIntegrable _ _
  · intro v hv
    rw [Set.mem_Ioo] at hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvs : |v| < θ := by rw [abs_lt]; constructor <;> linarith
    have hsv : |s - v| < θ := by rw [abs_lt]; constructor <;> linarith
    have h1 := cos_theta_lt_cos_of_abs_lt θ v hθπ hvs
    have h2 := cos_theta_lt_cos_of_abs_lt θ (s - v) hθπ hsv
    exact mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)

end Work.LinnikAreas.Density4
