import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIData
import Submission.Work.FTS_LocDatum3a.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `bump` vanishes on the three boundary lines -/

theorem bump_eq_zero_theta_zero (z : ℝ) : Work.FTS.StrongEps.bump z 0 = 0 := by
  show Work.FTS.StrongEps.zCut z * Work.FTS.StrongEps.thCut 0 = 0
  rw [Work.FTS.StrongEps.bump_thCut_eq_zero_of_lt (by linarith [Real.pi_pos]), mul_zero]

theorem bump_eq_zero_theta_pi (z : ℝ) : Work.FTS.StrongEps.bump z (Real.pi / 2) = 0 := by
  show Work.FTS.StrongEps.zCut z * Work.FTS.StrongEps.thCut (Real.pi / 2) = 0
  rw [Work.FTS.StrongEps.bump_thCut_eq_zero_of_gt (by linarith [Real.pi_pos]), mul_zero]

theorem bump_eq_zero_z_zero (θ : ℝ) : Work.FTS.StrongEps.bump 0 θ = 0 := by
  show Work.FTS.StrongEps.zCut 0 * Work.FTS.StrongEps.thCut θ = 0
  rw [Work.FTS.StrongEps.bump_zCut_eq_zero_of_lt (by norm_num : (0 : ℝ) < 1 / 2), zero_mul]

/-! ## `CoerAdm` of the projected mollified slice -/


end Work.FTS.StrongEps.EpsE4Thr
