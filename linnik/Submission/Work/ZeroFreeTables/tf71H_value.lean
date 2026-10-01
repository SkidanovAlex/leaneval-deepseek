import Mathlib
import Submission.Work.ZeroFreeTables.tf71H_defs

namespace Work.ZeroFreeTables

/-- Elementary evaluation of `tf71H` at the two endpoints `0` and `2γ` of the
support of the §7 test function: the difference collapses to HB Lemma 7.1's
`F 0 = 2(1+tan²θ)(1 − θ cot θ)²`. -/
theorem tf71H_value (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Work.ZeroFreeTables.tf71H θ lam (2 * Work.ZeroFreeTables.tf71γ θ lam) - Work.ZeroFreeTables.tf71H θ lam 0
      = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.tan θ)⁻¹) ^ 2 := by
  -- `tan θ ≠ 0`, `λ ≠ 0`, `sin θ ≠ 0`, `cos θ ≠ 0` are the non-vanishing facts
  have htan : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hsinθ : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  -- `ζ · (2γ) = 2θ`
  have hz : lam * Real.tan θ * (2 * (θ / (lam * Real.tan θ))) = 2 * θ := by
    field_simp
  -- unfold the antiderivative and the parameters
  simp only [tf71H, tf71ζ, tf71γ]
  rw [hz]
  -- evaluate the elementary values at `0` (the `x = 0` occurrences)
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, sub_zero, zero_div,
    show (0:ℝ)/2 = 0 from by norm_num, Real.cos_neg,
    show 2 * θ - 2 * θ = 0 from by ring, show θ - 2 * θ = -θ from by ring,
    mul_neg, zero_sub]
  -- express everything in `sin θ`, `cos θ`
  rw [Real.tan_eq_sin_div_cos θ, Real.sin_two_mul, Real.cos_two_mul]
  field_simp [hsinθ, hcosθ]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

end Work.ZeroFreeTables
