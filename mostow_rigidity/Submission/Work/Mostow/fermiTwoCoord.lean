import Mathlib
import Submission.Work.Mostow.fermiTwoDefs

/-!
# Coordinates and hyperbolic norm of the standard Fermi chart of `E 2`

`Work.Mostow.FermiTwo.lineStd s = sinh s • axis` is the standard unit-speed geodesic of the
hyperbolic plane `ℍ² = E 2`, and `stdFermi (s, r) = cosh r • lineStd s + sinh r • axisPerp`
is its standard Fermi chart.

This file computes, in the graph chart `u ↦ (u, √(1+‖u‖²))` of the hyperboloid:

* `tpart (lineStd s) = cosh s`, and the coordinates `(lineStd s) 0 = sinh s`, `(lineStd s) 1 = 0`;
* `tpart (stdFermi (s, r)) = cosh r * cosh s`, and the coordinates
  `(stdFermi (s, r)) 0 = cosh r * sinh s`, `(stdFermi (s, r)) 1 = sinh r`.

Equivalently: the hyperboloid points are `(sinh s, 0, cosh s)` and
`(cosh r sinh s, sinh r, cosh r cosh s)`.
-/

namespace Work.Mostow

open Submission.Mostow

namespace FermiTwo

noncomputable section

/-- The standard basis vectors of `E 2` used by this file are unit vectors. -/
lemma norm_axis : ‖(axis : E 2)‖ = 1 := by simp [axis]

lemma norm_axisPerp : ‖(axisPerp : E 2)‖ = 1 := by simp [axisPerp]

/-- `axis` and `axisPerp` are orthogonal. -/
lemma inner_axis_axisPerp : inner ℝ (axis : E 2) axisPerp = 0 := by
  rw [axis, axisPerp, EuclideanSpace.inner_single_right]; simp

/-- Norm of the standard line: `‖lineStd s‖ = |sinh s|`. -/
lemma norm_lineStd (s : ℝ) : ‖lineStd s‖ = |Real.sinh s| := by
  rw [lineStd, norm_smul, Real.norm_eq_abs, norm_axis, mul_one]

/-- The standard geodesic lies in the first coordinate axis. -/
lemma lineStd_apply_zero (s : ℝ) : (lineStd s : E 2) 0 = Real.sinh s := by
  simp [lineStd, axis]

lemma lineStd_apply_one (s : ℝ) : (lineStd s : E 2) 1 = 0 := by
  simp [lineStd, axis]

/-- Squared norm of the standard Fermi chart point, in coordinates along the orthonormal pair
`(axis, axisPerp)`. -/
lemma norm_sq_stdFermi (s r : ℝ) :
    ‖stdFermi (s, r)‖ ^ 2 = (Real.cosh r * Real.sinh s) ^ 2 + Real.sinh r ^ 2 := by
  have horth : inner ℝ ((Real.cosh r * Real.sinh s) • (axis : E 2))
      (Real.sinh r • axisPerp) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, inner_axis_axisPerp, mul_zero, mul_zero]
  rw [stdFermi_apply s r, norm_add_sq_real, horth, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, norm_axis, norm_axisPerp, mul_one, mul_one, sq_abs, sq_abs]
  ring

/-- First coordinate of the standard Fermi chart point. -/
lemma stdFermi_apply_zero (s r : ℝ) : (stdFermi (s, r) : E 2) 0 = Real.cosh r * Real.sinh s := by
  rw [stdFermi_apply]
  simp [axis, axisPerp]

/-- Second coordinate of the standard Fermi chart point. -/
lemma stdFermi_apply_one (s r : ℝ) : (stdFermi (s, r) : E 2) 1 = Real.sinh r := by
  rw [stdFermi_apply]
  simp [axis, axisPerp]

/-- Hyperbolic `tpart` of the standard line. -/
lemma tpart_lineStd (s : ℝ) : Submission.Mostow.tpart (lineStd s) = Real.cosh s := by
  rw [tpart, norm_lineStd, sq_abs]
  have h : 1 + Real.sinh s ^ 2 = Real.cosh s ^ 2 := by linarith [Real.cosh_sq s]
  rw [h, Real.sqrt_sq (Real.cosh_pos s).le]

/-- Hyperbolic `tpart` of the standard Fermi chart point. -/
lemma tpart_stdFermi (s r : ℝ) :
    Submission.Mostow.tpart (stdFermi (s, r)) = Real.cosh r * Real.cosh s := by
  rw [tpart, norm_sq_stdFermi]
  have key : 1 + ((Real.cosh r * Real.sinh s) ^ 2 + Real.sinh r ^ 2)
      = (Real.cosh r * Real.cosh s) ^ 2 := by
    nlinarith [Real.cosh_sq s, Real.cosh_sq r]
  rw [key, Real.sqrt_sq (mul_nonneg (Real.cosh_pos r).le (Real.cosh_pos s).le)]

end

end FermiTwo

theorem fermiTwoCoord :
    (∀ s : ℝ, Submission.Mostow.tpart (Work.Mostow.FermiTwo.lineStd s) = Real.cosh s) ∧
    (∀ s r : ℝ, (Work.Mostow.FermiTwo.stdFermi (s, r)) 0 = Real.cosh r * Real.sinh s) ∧
    (∀ s r : ℝ, (Work.Mostow.FermiTwo.stdFermi (s, r)) 1 = Real.sinh r) ∧
    (∀ s r : ℝ, Submission.Mostow.tpart (Work.Mostow.FermiTwo.stdFermi (s, r))
      = Real.cosh r * Real.cosh s) ∧
    (∀ s : ℝ, (Work.Mostow.FermiTwo.lineStd s) 0 = Real.sinh s) ∧
    (∀ s : ℝ, (Work.Mostow.FermiTwo.lineStd s) 1 = 0) ∧
    (∀ s : ℝ, Work.Mostow.FermiTwo.lineStd s
      = Real.sinh s • (Work.Mostow.FermiTwo.axis : Submission.Mostow.E 2)) :=
  ⟨FermiTwo.tpart_lineStd, FermiTwo.stdFermi_apply_zero, FermiTwo.stdFermi_apply_one,
   FermiTwo.tpart_stdFermi, FermiTwo.lineStd_apply_zero, FermiTwo.lineStd_apply_one,
   fun _ => rfl⟩

end Work.Mostow
