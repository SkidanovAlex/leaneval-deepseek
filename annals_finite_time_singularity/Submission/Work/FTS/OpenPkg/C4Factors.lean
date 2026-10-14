import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary bridges -/





/-! ## The angular moment `FK = Qang g 0` and the derivative of `L₁₂` -/

/-- The two normalisations of the angular weight agree. -/
theorem Ktheta_eq_K : Work.Elliptic.Ktheta = Work.Spaces.K := by
  funext θ
  simp [Work.Elliptic.Ktheta, Work.Spaces.K]

/-- `Work.Elliptic.Qang g 0` is `Work.Construction.FK g`. -/
theorem Qang_zero_eq_FK (g : ℝ → ℝ → ℝ) : Work.Elliptic.Qang g 0 = Work.Construction.FK g := by
  funext z
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_zero, Ktheta_eq_K]
  ring




/-! ## The radial functions `L₁₂(F_*)`, `FK g`, `FK(F_*)` -/




/-! ## The fixed profile and the perturbation, and their operators -/



/-! ## The residuals `Φ̃` and the operators `Rop`, `Uop`, `Vop` -/





/-! ## The bundle -/


end Work.FTS.OpenPkg
