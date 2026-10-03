import Mathlib
import Submission.Work.Repel.Koebe.ExteriorWindingDefs

namespace Work.Repel.Koebe

/-- `Φ g ζ` does not vanish on the disc of radius `r⁻¹` as soon as `g` omits the value `ζ` on
`{r ≤ ‖z‖}`: for `v ≠ 0` the two formulae `Φ g ζ v = v * (g v⁻¹ - ζ)` and `‖v⁻¹‖ ≥ r` show this,
while `Φ g ζ 0 = 1`. -/
theorem Phi_ne_zero {g : ℂ → ℂ} {ζ : ℂ} {r : ℝ} (hr : 0 < r)
    (hζ : ∀ z : ℂ, r ≤ ‖z‖ → g z ≠ ζ) :
    ∀ v : ℂ, ‖v‖ ≤ r⁻¹ → Work.Repel.Koebe.Phi g ζ v ≠ 0 := by
  intro v hv h
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [Phi_zero] at h
    exact one_ne_zero h
  · rw [Phi_apply g ζ hv0] at h
    have hnorm : r ≤ ‖v⁻¹‖ := by
      rw [norm_inv]
      have hx : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
      simpa [one_div] using one_div_le_one_div_of_le hx hv
    have hgz : g v⁻¹ = ζ := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hv0
      · exact sub_eq_zero.mp h1
    exact hζ v⁻¹ hnorm hgz

end Work.Repel.Koebe
