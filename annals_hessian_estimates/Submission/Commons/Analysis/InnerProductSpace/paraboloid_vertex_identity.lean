import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProductSpace

/-- Completing the square for the quadratic function `z ↦ ‖z - a‖ ^ 2 - m * ‖z - b‖ ^ 2`:
if `c` is the vertex, i.e. `(1 - m) • c = a - m • b`, then
`‖z - a‖ ^ 2 - m * ‖z - b‖ ^ 2 = (1 - m) * ‖z - c‖ ^ 2 + (vertex value)`. -/
private lemma norm_sub_sq_sub_smul_norm_sub_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℝ) {a b c : E} (hc : (1 - m) • c = a - m • b) (z : E) :
    ‖z - a‖ ^ 2 - m * ‖z - b‖ ^ 2
      = (1 - m) * ‖z - c‖ ^ 2 + (‖c - a‖ ^ 2 - m * ‖c - b‖ ^ 2) := by
  have hz1 : ‖z - a‖ ^ 2 = ‖z - c‖ ^ 2 + 2 * inner ℝ (z - c) (c - a) + ‖c - a‖ ^ 2 := by
    have h := norm_add_sq_real (z - c) (c - a)
    rw [show (z - c) + (c - a) = z - a by abel] at h
    exact h
  have hz2 : ‖z - b‖ ^ 2 = ‖z - c‖ ^ 2 + 2 * inner ℝ (z - c) (c - b) + ‖c - b‖ ^ 2 := by
    have h := norm_add_sq_real (z - c) (c - b)
    rw [show (z - c) + (c - b) = z - b by abel] at h
    exact h
  have hcross : inner ℝ (z - c) (c - a) - m * inner ℝ (z - c) (c - b) = 0 := by
    have h0 : (c - a) - m • (c - b) = 0 := by
      have h' : (c - a) - m • (c - b) = (1 - m) • c - (a - m • b) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [h', hc, sub_self]
    have h2 := congrArg (fun w => inner ℝ (z - c) w) h0
    rw [inner_zero_right, inner_sub_right, real_inner_smul_right] at h2
    exact h2
  rw [hz1, hz2]
  linear_combination (2 : ℝ) * hcross

theorem paraboloid_vertex_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {M : ℝ} (hM : M ≠ 1) {y₁ yb x₂ yt : E} (hrel : M • yb = y₁ + (M - 1) • x₂) :
    ∀ z : E, ‖z - y₁‖ ^ 2 - M * ‖z - yt‖ ^ 2
      = (1 - M) * ‖z - (x₂ + ((M - 1)⁻¹ * M) • (yt - yb))‖ ^ 2
        + (‖x₂ + ((M - 1)⁻¹ * M) • (yt - yb) - y₁‖ ^ 2
            - M * ‖x₂ + ((M - 1)⁻¹ * M) • (yt - yb) - yt‖ ^ 2) := by
  intro z
  have hM1 : M - 1 ≠ 0 := sub_ne_zero.mpr hM
  have hk : (1 - M) * ((M - 1)⁻¹ * M) = -M := by
    rw [show (1 : ℝ) - M = -(M - 1) by ring, neg_mul, ← mul_assoc, mul_inv_cancel₀ hM1,
      one_mul]
  have hc : (1 - M) • (x₂ + ((M - 1)⁻¹ * M) • (yt - yb)) = y₁ - M • yt := by
    rw [smul_add, smul_smul, hk, neg_smul, smul_sub]
    rw [hrel]
    have hx : (1 - M) • x₂ = -((M - 1) • x₂) := by
      rw [show (1 : ℝ) - M = -(M - 1) by ring, neg_smul]
    rw [hx]
    abel
  exact norm_sub_sq_sub_smul_norm_sub_sq M hc z

end Commons.Analysis.InnerProductSpace