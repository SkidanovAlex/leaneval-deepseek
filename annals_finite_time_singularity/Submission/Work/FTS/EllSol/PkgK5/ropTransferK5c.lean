import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.K5c.RopFinal
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The linking identity -/

/-- `ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)` for `θ ∈ (0,π/2)`. -/
theorem rop_eq_uop_vop_point {α : ℝ} {Ξ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ξ z θ
      = -2 * Real.sin θ ^ 2
          * (Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ)
        + Work.Construction.Vop Ξ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [hθ2, Real.pi_pos]))
  have hs2 : Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
  rw [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop, Work.Spaces.pz,
    Work.Spaces.pth, Real.tan_eq_sin_div_cos, hs2]
  field_simp
  ring

/-! ## The target -/


end Work.FTS.EllSol.PkgK5
