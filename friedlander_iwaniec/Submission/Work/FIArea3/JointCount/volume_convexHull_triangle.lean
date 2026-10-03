/-
# `Work.FIArea3.JointCount.volume_convexHull_triangle`

The area of the triangle with vertices `0`, `u`, `v` in `ℂ` (viewed as `ℝ²`) is the absolute
value of half the determinant `u.re * v.im - u.im * v.re`.

This is the same statement that is proved in
`Submission/Work/FIArea3/JointCount/volume_convexHull_zero_pair.lean` as
`Work.FIArea3.JointCount.volume_convexHull_zero_pair` (there the proof transports the standard
unit triangle along the real-linear map `z ↦ z.re • u + z.im • v`, whose determinant in the real
basis `{1, I}` of `ℂ` is exactly `u.re * v.im - u.im * v.re`).  We expose that result under the
name requested here.
-/
import Submission.Work.FIArea3.JointCount.volume_convexHull_zero_pair

namespace Work.FIArea3.JointCount

/-- **Area of the triangle spanned by `0`, `u`, `v` in `ℂ`.**
`(volume (convexHull ℝ {0, u, v})).toReal = |u.re * v.im - u.im * v.re| / 2`. -/
theorem volume_convexHull_triangle (u v : ℂ) :
    (MeasureTheory.volume (convexHull ℝ ({(0 : ℂ), u, v} : Set ℂ))).toReal
      = |u.re * v.im - u.im * v.re| / 2 :=
  volume_convexHull_zero_pair u v

end Work.FIArea3.JointCount
