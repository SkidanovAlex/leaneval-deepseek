import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpInterpolation

namespace Work.KMTAreas.A7

/-- Affine interpolation identity: for `c < b` the parameter
`(b - a) / (b - c)` lies in `[0,1]` when `c ≤ a ≤ b`, and the affine combination
`(1 - θ) * b + θ * c` equals `a`. -/
private lemma interp_affine {a b c : ℝ} (hcb : c < b) :
    (1 - (b - a) / (b - c)) * b + ((b - a) / (b - c)) * c = a := by
  have h : b - c ≠ 0 := ne_of_gt (sub_pos.mpr hcb)
  field_simp
  ring

theorem exists_interp_theta {q : ℝ} (hq₂ : 2 ≤ q) {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    (hq : q ≤ 2 * (k₀ : ℝ)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ q⁻¹ = (1 - θ) * (2 : ℝ)⁻¹ + θ * (2 * (k₀ : ℝ))⁻¹ := by
  have hq_pos : 0 < q := by linarith
  have hk2 : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have ht_pos : 0 < 2 * (k₀ : ℝ) := by linarith
  -- `q⁻¹` lies between the two endpoints `(2 * k₀)⁻¹` and `(2 : ℝ)⁻¹`.
  have hc_le_a : (2 * (k₀ : ℝ))⁻¹ ≤ q⁻¹ := (inv_le_inv₀ ht_pos hq_pos).mpr hq
  have ha_le_b : q⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hq_pos (by norm_num : (0 : ℝ) < 2)).mpr hq₂
  have ht_lt_b : 2 < 2 * (k₀ : ℝ) := by linarith
  have hc_lt_b : (2 * (k₀ : ℝ))⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ ht_pos (by norm_num : (0 : ℝ) < 2)).mpr ht_lt_b
  refine ⟨((2 : ℝ)⁻¹ - q⁻¹) / ((2 : ℝ)⁻¹ - (2 * (k₀ : ℝ))⁻¹), ?_, ?_, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr ha_le_b) (le_of_lt (sub_pos.mpr hc_lt_b))
  · rw [div_le_one (sub_pos.mpr hc_lt_b)]
    exact sub_le_sub_left hc_le_a _
  · rw [eq_comm]
    exact interp_affine hc_lt_b

end Work.KMTAreas.A7
