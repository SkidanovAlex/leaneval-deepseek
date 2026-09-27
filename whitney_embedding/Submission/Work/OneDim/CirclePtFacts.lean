import Submission.Work.OneDim.CirclePt

/-!
# The two stereographic coordinates in complex form

The definitions in `Submission.Work.OneDim.CirclePt` are stated with the real and imaginary parts
inside the complex number; this file records the complex form of `spherePt` and the first
round-trip identity, which are the workhorse computations for the remaining facts about
`spherePt`, `spherePt'`, `sphereCoord`, `sphereCoord'`.
-/

namespace Work.OneDim

open scoped Manifold ContDiff Topology
open Set

noncomputable section

/-- `spherePt t` as a complex number. -/
theorem spherePt_coe (t : ℝ) : ((spherePt t : Circle) : ℂ)
    = ((1 - t ^ 2) / (1 + t ^ 2) : ℝ) + ((2 * t) / (1 + t ^ 2) : ℝ) * Complex.I := by
  rw [spherePt_apply]
  push_cast [Complex.ofReal_div]
  ring_nf

/-- `spherePt' t` as a complex number. -/
theorem spherePt'_coe (t : ℝ) : ((spherePt' t : Circle) : ℂ)
    = ((t ^ 2 - 1) / (1 + t ^ 2) : ℝ) + ((2 * t) / (1 + t ^ 2) : ℝ) * Complex.I := by
  rw [spherePt'_apply]
  push_cast [Complex.ofReal_div]
  ring_nf

/-- The stereographic coordinate inverts `spherePt`. -/
theorem sphereCoord_spherePt (t : ℝ) : sphereCoord (spherePt t) = t := by
  rw [sphereCoord, spherePt_coe]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero]
  have h : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The other stereographic coordinate inverts `spherePt'`. -/
theorem sphereCoord'_spherePt' (t : ℝ) : sphereCoord' (spherePt' t) = t := by
  rw [sphereCoord', spherePt'_coe]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero]
  have h : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end

end Work.OneDim

namespace Work.OneDim

open scoped Manifold ContDiff Topology
open Set

noncomputable section

/-- The equation of the unit circle, in coordinates. -/
theorem circle_re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h : ‖(z : ℂ)‖ = 1 := by
    have hz := Metric.mem_sphere.mp z.2
    rwa [dist_eq_norm, sub_zero] at hz
  have h2 : Complex.normSq (z : ℂ) = 1 := by rw [Complex.normSq_eq_norm_sq, h]; norm_num
  rw [Complex.normSq_apply] at h2
  nlinarith [h2]

/-- A point of the circle different from `-1` has `1 + re ≠ 0`. -/
theorem circle_one_add_re_ne_zero (z : Circle) (hz : (z : ℂ) ≠ -1) : 1 + (z : ℂ).re ≠ 0 := by
  intro h
  apply hz
  have hre : (z : ℂ).re = -1 := by linarith
  have him : (z : ℂ).im = 0 := by
    have h := circle_re_sq_add_im_sq z
    rw [hre] at h
    nlinarith [h]
  refine Complex.ext ?_ ?_ <;> simp [hre, him]

/-- A point of the circle different from `1` has `1 - re ≠ 0`. -/
theorem circle_one_sub_re_ne_zero (z : Circle) (hz : (z : ℂ) ≠ 1) : 1 - (z : ℂ).re ≠ 0 := by
  intro h
  apply hz
  have hre : (z : ℂ).re = 1 := by linarith
  have him : (z : ℂ).im = 0 := by
    have h := circle_re_sq_add_im_sq z
    rw [hre] at h
    nlinarith [h]
  refine Complex.ext ?_ ?_ <;> simp [hre, him]

/-- `spherePt` is injective (its stereographic coordinate is a left inverse). -/
theorem spherePt_injective : Function.Injective spherePt := by
  intro a b hab
  have h := congrArg (fun z : Circle => sphereCoord (z : ℂ)) hab
  simpa only [sphereCoord_spherePt] using h

/-- `spherePt` misses the point `-1`. -/
theorem spherePt_ne_Qm (t : ℝ) : spherePt t ≠ Qm := by
  intro h
  have hre : ((spherePt t : Circle) : ℂ).re = -1 := by
    rw [h]; simp [Qm_coe]
  rw [spherePt_coe] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero] at hre
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp at hre
  linarith

/-- The complex form of a point of the circle is determined by its real and imaginary parts. -/
theorem circle_ext' {z w : Circle} (hre : (z : ℂ).re = (w : ℂ).re) (him : (z : ℂ).im = (w : ℂ).im) :
    z = w := by
  refine Subtype.ext ?_
  exact Complex.ext hre him

/-- The two parametrisations are related by `t ↦ 1/t`. -/
theorem spherePt'_eq_spherePt_inv (t : ℝ) (ht : t ≠ 0) : spherePt' t = spherePt (1 / t) := by
  refine circle_ext' ?_ ?_
  · rw [spherePt'_coe, spherePt_coe]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero]
    field_simp
    ring
  · rw [spherePt'_coe, spherePt_coe]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_mul, add_zero]
    field_simp
    ring

/-! The remaining facts are: the round-trip identities `spherePt (sphereCoord z) = z` for
`(z : ℂ) ≠ -1` and `spherePt' (sphereCoord' z) = z` for `(z : ℂ) ≠ 1` (both reduce, after clearing
the denominators `1 + re` resp. `1 - re`, to the single polynomial identity
`re^2 + im^2 = 1`, proved above as `circle_re_sq_add_im_sq`), the analogous injectivity and range
statements for `spherePt'`, and the local-diffeomorphism properties of `spherePt` and of the germ
`s ↦ spherePt (s / (A + B * s))`. -/

end

end Work.OneDim
