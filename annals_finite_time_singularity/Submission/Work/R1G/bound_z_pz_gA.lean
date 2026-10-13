import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Boundedness of `z · ∂_z gA` on the quadrant

For the analytic perturbation `gA z θ = Zf z · Tf θ` (`Zf z = z²/(1+z²)⁴`, `Tf θ = sin (2θ)`)
we show that the weighted radial derivative `D_z gA = z ∂_z gA` is *bounded* on the quadrant
`z ≥ 0`, `θ ∈ [0,π/2]`, with the explicit (crude) constant `8`.

Indeed `∂_z gA z θ = Zf'(z) · Tf θ` (`pz_gA`), so

  `z · ∂_z gA z θ = (z · Zf'(z)) · Tf θ = Zf1 z · Tf θ`   (`Zf1_eq`),

and it remains to bound the rational function `Zf1 z = (2z² - 6z⁴)/(1+z²)⁵` and the angular
factor `|sin (2θ)| ≤ 1`.
-/

/-- The radial factor `z ↦ z · Zf'(z) = (2z² - 6z⁴)/(1+z²)⁵` is bounded by `8` on all of `ℝ`,
a fortiori on `z ≥ 0`.  The bound is crude; only its existence matters. -/
lemma abs_Zf1_le (z : ℝ) : |Zf1 z| ≤ 8 := by
  have ht : (1 : ℝ) ≤ 1 + z ^ 2 := by linarith [sq_nonneg z]
  have hden : 0 < (1 + z ^ 2) ^ 5 := by positivity
  have hP1 : 1 + z ^ 2 ≤ (1 + z ^ 2) ^ 5 := by
    simpa using pow_le_pow_right₀ (m := 1) (n := 5) ht (by norm_num : (1 : ℕ) ≤ 5)
  have hP2 : (1 + z ^ 2) ^ 2 ≤ (1 + z ^ 2) ^ 5 :=
    pow_le_pow_right₀ (m := 2) (n := 5) ht (by norm_num)
  have hz2 : z ^ 2 ≤ (1 + z ^ 2) ^ 5 := le_trans (by linarith [sq_nonneg z]) hP1
  have hz4 : z ^ 4 ≤ (1 + z ^ 2) ^ 5 := by
    calc z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ ≤ (1 + z ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg z) (by linarith [sq_nonneg z]) 2
      _ ≤ (1 + z ^ 2) ^ 5 := hP2
  rw [Zf1, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have ha : |2 * z ^ 2 - 6 * z ^ 4| ≤ 2 * z ^ 2 + 6 * z ^ 4 := by
    rw [sub_eq_add_neg]
    calc |2 * z ^ 2 + -(6 * z ^ 4)| ≤ |2 * z ^ 2| + |-(6 * z ^ 4)| := abs_add_le _ _
      _ = 2 * z ^ 2 + 6 * z ^ 4 := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * z ^ 2), abs_neg,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * z ^ 4)]
  linarith

theorem bound_z_pz_gA :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z * Work.Spaces.pz Work.R1G.gA z θ| ≤ C := by
  refine ⟨8, by norm_num, ?_⟩
  intro z θ hz hθ
  rw [Work.R1G.pz_gA]
  rw [show z * (deriv Zf z * Tf θ) = Zf1 z * Tf θ by rw [← mul_assoc, Zf1_eq]]
  rw [abs_mul]
  calc |Zf1 z| * |Tf θ| ≤ 8 * 1 :=
        mul_le_mul (abs_Zf1_le z) (abs_Tf_le_one θ) (abs_nonneg _) (by norm_num)
    _ = 8 := by norm_num

end Work.R1G
