import Mathlib

namespace Work.Pert.Ksub2

/-- Lipschitz-near-a-point from a derivative: if `‖A‖ < C` then near `a` the map `f` is
`C`-Lipschitz with respect to its value at `a`. -/
private theorem eventually_norm_sub_le_of_hasDerivAt {f : ℂ → ℂ} {a A : ℂ}
    (h : HasDerivAt f A a) {C : ℝ} (hC : ‖A‖ < C) :
    ∀ᶠ z in nhds a, ‖f z - f a‖ ≤ C * ‖z - a‖ := by
  have hc : 0 < C - ‖A‖ := sub_pos.mpr hC
  have hev := h.isLittleO.def (c := C - ‖A‖) hc
  filter_upwards [hev] with z hz
  have h2 : ‖(z - a) • A‖ ≤ ‖A‖ * ‖z - a‖ := by rw [norm_smul, mul_comm]
  have h1 : ‖(f z - f a - (z - a) • A) + (z - a) • A‖
      ≤ ‖f z - f a - (z - a) • A‖ + ‖(z - a) • A‖ := norm_add_le _ _
  rw [sub_add_cancel] at h1
  calc ‖f z - f a‖
      ≤ (C - ‖A‖) * ‖z - a‖ + ‖A‖ * ‖z - a‖ := le_trans h1 (add_le_add hz h2)
    _ = C * ‖z - a‖ := by ring

theorem exists_ball_local_inverse {φ ψ : ℂ → ℂ} {a u A : ℂ} (hψu : ψ a = u)
    (hright : ∀ᶠ z in nhds a, φ (ψ z) = z) (hψ : HasDerivAt ψ A a)
    {c : ℝ} (hc : 0 < c) (hA : ‖A‖ ≤ c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z - a‖ < ρ →
      φ (ψ z) = z ∧ ‖ψ z - u‖ ≤ 2 * c * ‖z - a‖ := by
  have hC : ‖A‖ < 2 * c := lt_of_le_of_lt hA (by linarith)
  obtain ⟨ρ₁, hρ₁, h₁⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_norm_sub_le_of_hasDerivAt hψ hC)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.eventually_nhds_iff.mp hright
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ⟨?_, ?_⟩⟩
  · exact h₂ (y := z) (by rw [dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_right _ _))
  · have h := h₁ (y := z) (by rw [dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_left _ _))
    simpa [hψu] using h

end Work.Pert.Ksub2
