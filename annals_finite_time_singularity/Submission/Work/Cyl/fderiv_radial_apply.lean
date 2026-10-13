import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

theorem fderiv_radial_apply (x v : Work.Cyl.R3) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ Work.Cyl.radial x v = (x 0 * v 0 + x 1 * v 1) / Work.Cyl.radial x := by
  have hd : DifferentiableAt ℝ radial x := differentiableAt_radial x (ne_of_gt hr)
  rw [fderiv_apply_eq_deriv_line radial x v hd]
  -- the derivative along the line `t ↦ x + t • v` of the squared radius
  have h0 : HasDerivAt (fun t : ℝ => x 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (x 0)
  have h1 : HasDerivAt (fun t : ℝ => x 1 + t * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (x 1)
  have hradsq : HasDerivAt (fun t : ℝ => radSq (x + t • v))
      (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
    have hfun : (fun t : ℝ => radSq (x + t • v)) =
        fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1) := by
      funext t; simp [radSq, pow_two]
    rw [hfun]
    have h := (h0.mul h0).add (h1.mul h1)
    convert h using 1
    ring
  have hne : radSq (x + (0:ℝ) • v) ≠ 0 := by
    rw [zero_smul, add_zero, ← radial_sq]
    exact pow_ne_zero 2 (ne_of_gt hr)
  -- `radial` is `Real.sqrt ∘ radSq`, so the chain rule with `Real.hasDerivAt_sqrt` applies
  have hmain : (fun t : ℝ => radial (x + t • v)) =
      fun t : ℝ => Real.sqrt (radSq (x + t • v)) := by
    funext t; rw [radial]
  rw [hmain]
  have hder := hradsq.sqrt hne
  have hval : (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) / (2 * Real.sqrt (radSq (x + (0:ℝ) • v)))
      = (x 0 * v 0 + x 1 * v 1) / radial x := by
    rw [zero_smul, add_zero, radial]
    have hpos : 0 < radSq x := by rw [← radial_sq]; positivity
    have hsne : Real.sqrt (radSq x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
  rw [hval] at hder
  exact hder.deriv

end Work.Cyl
