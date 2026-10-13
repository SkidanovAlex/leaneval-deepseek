import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm
import Submission.Work.Cyl.norm_angularVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open scoped Matrix

/-- The displacement of a rotation about the `x₃`-axis by the angle `h` is, in coordinates,
`((cos h - 1) x₀ - sin h x₁, sin h x₀ + (cos h - 1) x₁, 0)`. -/
theorem rotLE_sub_eq (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    Work.ConstructionInstance.rotLE h x - x
      = !₂[(Real.cos h - 1) * x 0 - Real.sin h * x 1,
           Real.sin h * x 0 + (Real.cos h - 1) * x 1, 0] := by
  ext i
  fin_cases i <;>
    simp [Work.ConstructionInstance.rotLE_apply, Work.ConstructionInstance.rotCoord] <;> ring

/-- Squared form of the displacement bound: the axis is fixed by `rotLE`, so the squared
displacement is `(2 - 2 cos h) r²`, where `r = Work.Cyl.radial x` is the distance to the axis. -/
theorem norm_rotLE_sub_sq (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    ‖Work.ConstructionInstance.rotLE h x - x‖ ^ 2
      = (2 - 2 * Real.cos h) * Work.Cyl.radSq x := by
  rw [rotLE_sub_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [Work.Cyl.radSq]
  norm_num
  ring_nf
  linear_combination ((x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2) * Real.cos_sq_add_sin_sq h

/-- **Rotation about the symmetry axis moves a point by at most `|h|` times its distance to the
axis.**  Since `rotLE h` is the rotation by the angle `h` about the `x₃`-axis, it fixes the axial
coordinate and rotates the planar part, so the displacement lies in the plane and its length is
`|x|·|e^{ih} - 1| = |x|·√(2 - 2 cos h) ≤ |x|·|h|`. -/
theorem norm_rotLE_sub_le (h : ℝ) (x : Work.FTS.BSSwirl.R3) :
    ‖Work.ConstructionInstance.rotLE h x - x‖ ≤ |h| * Work.Cyl.radial x := by
  have hle : (2 - 2 * Real.cos h) * Work.Cyl.radSq x ≤ h ^ 2 * Work.Cyl.radSq x := by
    have hc : 1 - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
    have hr : 0 ≤ Work.Cyl.radSq x := Work.Cyl.radSq_nonneg x
    nlinarith
  have hb : 0 ≤ |h| * Work.Cyl.radial x :=
    mul_nonneg (abs_nonneg h) (Work.Cyl.radial_nonneg x)
  have hsq : ‖Work.ConstructionInstance.rotLE h x - x‖ ^ 2
      ≤ (|h| * Work.Cyl.radial x) ^ 2 := by
    rw [norm_rotLE_sub_sq]
    have hsqr : (|h| * Work.Cyl.radial x) ^ 2 = h ^ 2 * Work.Cyl.radSq x := by
      rw [mul_pow, sq_abs, Work.Cyl.radial_sq]
    rw [hsqr]
    exact hle
  have h' := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb] at h'

end Work.FTS.BSSwirl
