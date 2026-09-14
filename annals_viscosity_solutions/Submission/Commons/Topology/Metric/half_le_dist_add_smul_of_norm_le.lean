import Mathlib.Analysis.Normed.Module.Basic

namespace Commons.Topology.Metric

theorem half_le_dist_add_smul_of_norm_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {x δ M r : ℝ} {p q z₁ z₂ : G}
    (hM : 0 < M) (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M) (hδ : 0 ≤ δ)
    (hr : r = δ / (4 * M)) (hx : |x| ≤ r) (hd : δ ≤ dist p q) :
    δ / 2 ≤ dist (p + x • z₁) (q + x • z₂) := by
  have h4Mpos : (0 : ℝ) < 4 * M := by positivity
  have h4Mnonneg : (0 : ℝ) ≤ δ / (4 * M) := div_nonneg hδ (le_of_lt h4Mpos)
  have hx' : |x| ≤ δ / (4 * M) := by rw [hr] at hx; exact hx
  -- rewrite both sides as norms
  rw [dist_eq_norm] at hd ⊢
  have hdist : (p + x • z₁) - (q + x • z₂) = (p - q) + x • (z₁ - z₂) := by
    rw [smul_sub]
    abel
  rw [hdist]
  -- reverse triangle inequality
  have hnorm : ‖p - q‖ - ‖x • (z₁ - z₂)‖ ≤ ‖(p - q) + x • (z₁ - z₂)‖ := by
    have h := norm_sub_le ((p - q) + x • (z₁ - z₂)) (x • (z₁ - z₂))
    simp only [add_sub_cancel_right] at h
    linarith
  -- bound the perturbation
  have h3 : ‖x • (z₁ - z₂)‖ ≤ δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hz : ‖z₁ - z₂‖ ≤ 2 * M := by
      have h := norm_sub_le z₁ z₂
      linarith
    calc |x| * ‖z₁ - z₂‖ ≤ (δ / (4 * M)) * (2 * M) :=
          mul_le_mul hx' hz (norm_nonneg _) h4Mnonneg
      _ = δ / 2 := by field_simp; ring
  linarith

end Commons.Topology.Metric