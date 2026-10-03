import Mathlib

namespace Work.Pert.OmArc

/-- The trigonometric core of `geom_arc`: on `[π/2, 3π/2]` one has `cos θ - |sin θ| ≤ -1`.
Indeed `cos θ ≤ 0` there, so `cos θ - |sin θ| = -(|cos θ| + |sin θ|)`, and
`|cos θ| + |sin θ| ≥ 1` because its square is `cos²θ + sin²θ + 2|cos θ||sin θ| = 1 + 2|cos θ sin θ| ≥ 1`.
Equality is attained at `π/2`, `π` and `3π/2`. -/
theorem cos_sub_abs_sin_le_neg_one {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) :
    Real.cos θ - |Real.sin θ| ≤ -1 := by
  have hcos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
  have hcosabs : Real.cos θ = -|Real.cos θ| := by
    rw [abs_of_nonpos hcos]; ring
  have hkey : 1 ≤ |Real.cos θ| + |Real.sin θ| := by
    have hsq : (1 : ℝ) ^ 2 ≤ (|Real.cos θ| + |Real.sin θ|) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (Real.cos θ), sq_abs (Real.sin θ),
        abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]
    have h2 : 0 ≤ |Real.cos θ| + |Real.sin θ| := by positivity
    have h3 : |(1 : ℝ)| ≤ |(|Real.cos θ| + |Real.sin θ|)| := (sq_le_sq).mp hsq
    rwa [abs_one, abs_of_nonneg h2] at h3
  linarith [hcosabs, hkey]

/-- For `η > 0` and `θ ∈ [π/2, 3π/2]`, the point `η e^{iθ}` satisfies
`Re (η e^{iθ}) - |Im (η e^{iθ})| ≤ -η` (the maximum of `cos θ - |sin θ|` on the interval is `-1`). -/
theorem geom_arc {η θ : ℝ} (hη : 0 < η)
    (hθ : θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) :
    (η * Complex.exp (θ * Complex.I)).re - |(η * Complex.exp (θ * Complex.I)).im| ≤ -η := by
  have hre : (η * Complex.exp (θ * Complex.I)).re = η * Real.cos θ := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (η * Complex.exp (θ * Complex.I)).im = η * Real.sin θ := by
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  have hmul := mul_le_mul_of_nonneg_left (cos_sub_abs_sin_le_neg_one hθ) (le_of_lt hη)
  rw [abs_mul, abs_of_pos hη]
  nlinarith [hmul]

end Work.Pert.OmArc
