import Mathlib
import Submission.Work.Pert.CoordDefs

/-!
# PERT · `Work.Pert.OmArc.geom_Om`

The cone quantity `ζ ↦ Re ζ - |Im ζ|` on the two discs `Om η` (radius `13η/40` about `±iη`).

On the upper disc the quantity is `Re ζ - Im ζ` (the imaginary part is positive there because
`13/40 < 1`), which is maximized in the direction `(1,-1)/√2`; the sharp bound
`x - y ≤ √2 ‖z‖` for `z = x + iy` is obtained from `|Re (z(1+i))| ≤ ‖z‖·‖1+i‖`.  The lower disc
is handled with the mirror combination `x + y`, using `|Re (z(1-i))| ≤ ‖z‖·‖1-i‖`.
Both arguments are uniform in the sign of `η`: the hypothesis `‖w‖ ≤ 13η/40` already forces
`η ≥ 0`, and for `η ≤ 0` there is nothing in the discs (`Om η` is empty for `η < 0`).
-/

namespace Work.Pert.OmArc

/-- Sharp Cauchy–Schwarz in the direction `(1,-1)`: for `w = x + iy`,
`|x - y| ≤ √2 ‖w‖`.  Proof: `x - y = Re (w (1+i))` and `‖1+i‖ = √2`. -/
theorem abs_re_sub_im_le (w : ℂ) : |w.re - w.im| ≤ ‖w‖ * Real.sqrt 2 := by
  have hre : (w * (1 + Complex.I)).re = w.re - w.im := by
    simp [Complex.mul_re]
  have hnorm : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
    rw [Complex.norm_def, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    norm_num
  calc |w.re - w.im| = |(w * (1 + Complex.I)).re| := by rw [hre]
    _ ≤ ‖w * (1 + Complex.I)‖ := Complex.abs_re_le_norm _
    _ = ‖w‖ * ‖(1 : ℂ) + Complex.I‖ := norm_mul w _
    _ = ‖w‖ * Real.sqrt 2 := by rw [hnorm]

/-- Sharp Cauchy–Schwarz in the direction `(1,1)`: for `w = x + iy`,
`|x + y| ≤ √2 ‖w‖`.  Proof: `x + y = Re (w (1-i))` and `‖1-i‖ = √2`. -/
theorem abs_re_add_im_le (w : ℂ) : |w.re + w.im| ≤ ‖w‖ * Real.sqrt 2 := by
  have hre : (w * (1 - Complex.I)).re = w.re + w.im := by
    simp [Complex.mul_re]
  have hnorm : ‖(1 : ℂ) - Complex.I‖ = Real.sqrt 2 := by
    rw [Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
  calc |w.re + w.im| = |(w * (1 - Complex.I)).re| := by rw [hre]
    _ ≤ ‖w * (1 - Complex.I)‖ := Complex.abs_re_le_norm _
    _ = ‖w‖ * ‖(1 : ℂ) - Complex.I‖ := norm_mul w _
    _ = ‖w‖ * Real.sqrt 2 := by rw [hnorm]

/-- Every point of the closed disc of radius `13η/40` about `iη` satisfies the cone bound. -/
theorem geom_Om_upper (η : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 13 * η / 40) :
    (Complex.I * (η : ℂ) + w).re - |(Complex.I * (η : ℂ) + w).im|
      ≤ -η + 13 * Real.sqrt 2 / 40 * η := by
  -- the radius is nonnegative, hence so is `η`
  have hη : 0 ≤ η := by nlinarith [norm_nonneg w]
  have hIm : (Complex.I * (η : ℂ) + w).im = η + w.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hRe : (Complex.I * (η : ℂ) + w).re = w.re := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  -- the imaginary part is `≥ η - 13η/40 = 27η/40 ≥ 0`
  have him : 0 ≤ (Complex.I * (η : ℂ) + w).im := by
    rw [hIm]
    have h1 : -w.im ≤ ‖w‖ := le_trans (neg_le_abs w.im) (Complex.abs_im_le_norm w)
    nlinarith
  rw [abs_of_nonneg him, hIm, hRe]
  have key : w.re - w.im ≤ ‖w‖ * Real.sqrt 2 :=
    le_trans (le_abs_self _) (abs_re_sub_im_le w)
  have h2 : ‖w‖ * Real.sqrt 2 ≤ (13 * η / 40) * Real.sqrt 2 :=
    mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg 2)
  have h3 : (13 * η / 40) * Real.sqrt 2 = 13 * Real.sqrt 2 / 40 * η := by ring
  linarith

/-- Every point of the closed disc of radius `13η/40` about `-iη` satisfies the cone bound. -/
theorem geom_Om_lower (η : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 13 * η / 40) :
    (-(Complex.I * (η : ℂ)) + w).re - |(-(Complex.I * (η : ℂ)) + w).im|
      ≤ -η + 13 * Real.sqrt 2 / 40 * η := by
  have hη : 0 ≤ η := by nlinarith [norm_nonneg w]
  have hIm : (-(Complex.I * (η : ℂ)) + w).im = w.im - η := by
    simp [Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hRe : (-(Complex.I * (η : ℂ)) + w).re = w.re := by
    simp [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  -- the imaginary part is `≤ -η + 13η/40 = -27η/40 ≤ 0`
  have him : (-(Complex.I * (η : ℂ)) + w).im ≤ 0 := by
    rw [hIm]
    have h1 : w.im ≤ ‖w‖ := le_trans (le_abs_self w.im) (Complex.abs_im_le_norm w)
    nlinarith
  rw [abs_of_nonpos him, hIm, hRe]
  have key : w.re + w.im ≤ ‖w‖ * Real.sqrt 2 :=
    le_trans (le_abs_self _) (abs_re_add_im_le w)
  have h2 : ‖w‖ * Real.sqrt 2 ≤ (13 * η / 40) * Real.sqrt 2 :=
    mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg 2)
  have h3 : (13 * η / 40) * Real.sqrt 2 = 13 * Real.sqrt 2 / 40 * η := by ring
  linarith

/-- For `ζ` in `Om η` (the union of the two closed discs of radius `13η/40` about `±iη`,
`Work.Pert.Om`), the cone quantity `Re ζ - |Im ζ|` is at most `-η + (13√2/40)·η`. -/
theorem geom_Om {η : ℝ} {ζ : ℂ} (hζ : ζ ∈ Work.Pert.Om η) :
    ζ.re - |ζ.im| ≤ -η + 13 * Real.sqrt 2 / 40 * η := by
  rw [Work.Pert.Om, Set.mem_union] at hζ
  rcases hζ with h | h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have hw : ‖ζ - Complex.I * (η : ℂ)‖ ≤ 13 * η / 40 := h
    have hz : Complex.I * (η : ℂ) + (ζ - Complex.I * (η : ℂ)) = ζ := by ring
    have hg := geom_Om_upper η (ζ - Complex.I * (η : ℂ)) hw
    rwa [hz] at hg
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] at h
    have hw : ‖ζ + Complex.I * (η : ℂ)‖ ≤ 13 * η / 40 := h
    have hz : -(Complex.I * (η : ℂ)) + (ζ + Complex.I * (η : ℂ)) = ζ := by ring
    have hg := geom_Om_lower η (ζ + Complex.I * (η : ℂ)) hw
    rwa [hz] at hg

end Work.Pert.OmArc
