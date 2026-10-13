import Mathlib.Analysis.Real.Sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

/-- For `M ≥ 1` and `a, b ≥ 4M+1`, the sum of the reciprocal square roots is at most the
reciprocal square root of `M`.  Indeed `√a ≥ √(4M+1) ≥ √(4M) = 2√M`. -/
theorem inv_sqrt_add_inv_sqrt_le {M a b : ℝ} (hM : 1 ≤ M) (ha : 4 * M + 1 ≤ a)
    (hb : 4 * M + 1 ≤ b) : 1 / Real.sqrt a + 1 / Real.sqrt b ≤ 1 / Real.sqrt M := by
  have hMpos : 0 < M := by linarith
  have h4Mpos : 0 < 4 * M := by linarith
  have h4M1pos : 0 < 4 * M + 1 := by linarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hsqrt4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hsqrt4M : Real.sqrt (4 * M) = 2 * Real.sqrt M := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) M, hsqrt4]
  have hle : Real.sqrt (4 * M) ≤ Real.sqrt (4 * M + 1) := Real.sqrt_le_sqrt (by linarith)
  have hhalf : (1:ℝ) / (2 * Real.sqrt M) + 1 / (2 * Real.sqrt M) = 1 / Real.sqrt M := by
    have hne : Real.sqrt M ≠ 0 := ne_of_gt hsqrtM
    field_simp
    ring
  have key : ∀ x : ℝ, 4 * M + 1 ≤ x → 1 / Real.sqrt x ≤ 1 / (2 * Real.sqrt M) := by
    intro x hx
    have h1 : 1 / Real.sqrt x ≤ 1 / Real.sqrt (4 * M + 1) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr h4M1pos) (Real.sqrt_le_sqrt hx)
    have h2 : 1 / Real.sqrt (4 * M + 1) ≤ 1 / Real.sqrt (4 * M) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr h4Mpos) hle
    have h3 : 1 / Real.sqrt (4 * M) = 1 / (2 * Real.sqrt M) := by rw [hsqrt4M]
    linarith
  have hA := key a ha
  have hB := key b hb
  linarith

end Work.EllipticEst.ModalSolution
