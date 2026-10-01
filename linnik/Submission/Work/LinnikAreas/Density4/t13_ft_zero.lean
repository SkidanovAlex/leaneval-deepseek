import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

namespace Work.LinnikAreas.Density4

/-- At `x = 0` the (clamped) closed form of `f = g ⊛ g` of HB §7 collapses to the closed value
`λ̂ (1 + tan²θ) (3 - θ tan θ - 3θ/tan θ)` used in HB's Table 13: the branch condition
`0 ≤ 2γ` holds because `π/2 < θ < π` gives `tan θ < 0`, hence `ζ = -λ̂ tan θ > 0` and `γ > 0`;
what is left is the trigonometric identity
`λ̂²(1+tan²θ)² (2γ(1/2+cos²θ) - sin 2θ/(2ζ) - 2 cos θ sin θ/ζ) = λ̂(1+tan²θ)(3 - θ tan θ - 3θ/tan θ)`,
which reduces to `1 + tan²θ = 1/cos²θ` and `sin²θ + cos²θ = 1` after clearing denominators. -/
theorem t13_ft_zero (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    Work.LinnikAreas.Density4.fT θ lam 0 =
      lam * (1 + Real.tan θ ^ 2) * (3 - θ * Real.tan θ - 3 * θ / Real.tan θ) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hθ2
  have hc : Real.cos θ ≠ 0 := by
    intro h
    have := cos_neg_of_gt_half_pi hθ1 hθ2
    rw [h] at this
    linarith
  have hsq : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq θ
  have hγ : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  have hζ : 0 < zetaT θ lam := zetaT_pos hθ1 hθ2 hlam
  rw [fT, if_pos ⟨le_refl 0, by linarith⟩]
  simp only [mul_zero, sub_zero, zero_sub, Real.cos_zero, Real.sin_neg]
  rw [gammaT, zetaT, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp
  rw [hsq, one_mul]
  nlinarith [hsq, sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]

end Work.LinnikAreas.Density4
