import Mathlib
import Submission.Work.Mostow.fermiTwoDefs

/-!
# The standard geodesic line is arclength parametrised

`lineStd s = sinh s • axis` is the unit-speed geodesic of `E 2` issued from the base point `0`
along the first coordinate axis.  This file computes

`hdist (lineStd a) (lineStd b) = |a - b|`,

i.e. `s` is the hyperbolic arclength parameter on `lineStd`.

The computation is the explicit one in the hyperboloid chart: `tpart (lineStd s) = cosh s` and
`inner ℝ (lineStd a) (lineStd b) = sinh a * sinh b`, so the argument of `arcosh` in `hdist` is
`cosh a cosh b - sinh a sinh b = cosh (a - b)`, and `arcosh (cosh x) = |x|`.
-/

namespace Work.Mostow

open Submission.Mostow

namespace FermiTwo

noncomputable section

/-- `axis` is a unit vector. -/
private lemma norm_axis : ‖axis‖ = (1 : ℝ) := by
  simp [axis]

/-- `axis` has unit square length, hence `inner ℝ axis axis = 1`. -/
private lemma inner_axis_axis : inner ℝ (axis : E 2) axis = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_axis]
  norm_num

/-- The hyperboloid time coordinate of `lineStd s` is `cosh s`. -/
private lemma tpart_lineStd (s : ℝ) : tpart (lineStd s) = Real.cosh s := by
  have hs : lineStd s = Real.sinh s • axis := rfl
  rw [hs, tpart, norm_smul, Real.norm_eq_abs, norm_axis, mul_one, sq_abs, ← Real.cosh_sq']
  exact Real.sqrt_sq (le_of_lt (Real.cosh_pos s))

/-- The Euclidean inner product of two points of `lineStd`. -/
private lemma inner_lineStd (a b : ℝ) :
    inner ℝ (lineStd a) (lineStd b) = Real.sinh a * Real.sinh b := by
  have ha : lineStd a = Real.sinh a • axis := rfl
  have hb : lineStd b = Real.sinh b • axis := rfl
  rw [ha, hb, real_inner_smul_left, real_inner_smul_right, inner_axis_axis, mul_one]

end

end FermiTwo

theorem hdistLineStd (a b : ℝ) :
    Submission.Mostow.hdist (Work.Mostow.FermiTwo.lineStd a) (Work.Mostow.FermiTwo.lineStd b)
      = |a - b| := by
  have harg : tpart (FermiTwo.lineStd a) * tpart (FermiTwo.lineStd b)
      - inner ℝ (FermiTwo.lineStd a) (FermiTwo.lineStd b) = Real.cosh (a - b) := by
    rw [FermiTwo.tpart_lineStd, FermiTwo.tpart_lineStd, FermiTwo.inner_lineStd, Real.cosh_sub]
  rw [hdist, harg, ← Real.cosh_abs]
  exact Real.arcosh_cosh (abs_nonneg _)

end Work.Mostow
