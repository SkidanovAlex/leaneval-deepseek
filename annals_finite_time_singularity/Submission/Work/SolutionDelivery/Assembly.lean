import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.LocData.ZfarFstar.ZFBasic
import Submission.Work.LWP.VorticityAPI
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Defs
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.FTS.LocData.ZfarFstar.ZFMaj =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData
namespace ZF

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## `rpow` bookkeeping for the two weights -/

theorem rpow_neg_half_sq (S : ℝ) (hS : 0 ≤ S) (a : ℝ) :
    (S ^ (-(a / 2))) ^ 2 = S ^ (-a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
  congr 1
  push_cast
  ring

/-- `(x·(w/S^{a/2}))² = (x·w)²·S^{-a}`. -/
theorem mul_div_rpow_sq (x w S : ℝ) (hS : 0 ≤ S) (a : ℝ) :
    (x * (w / S ^ (a / 2))) ^ 2 = (x * w) ^ 2 * S ^ (-a) := by
  rw [div_eq_mul_inv]
  have h1 : (S ^ (a / 2))⁻¹ = S ^ (-(a / 2)) := (Real.rpow_neg hS (a / 2)).symm
  rw [h1]
  rw [show x * (w * S ^ (-(a / 2))) = (x * w) * S ^ (-(a / 2)) by ring]
  rw [mul_pow, rpow_neg_half_sq S hS a]

/-- `(x·Wt)² = (x·w)²·sin(2θ)^{-γ}`. -/
theorem mul_Wt_sq (x : ℝ) (z θ : ℝ) (α : ℝ) (hS : 0 ≤ Real.sin (2 * θ)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [show x * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
      = (x * Work.Spaces.w z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) by ring]
  rw [mul_pow, rpow_neg_half_sq _ hS (Work.Spaces.gam α)]

/-! ## The mixed derivatives of the far part -/


/-! ## The majorant -/


end ZF
end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.Top.BKM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- **The interval-integrability of the BKM integrand** for a `BlowupAt`: the top-namespace form
of `Work.FTS.Top.Integrable.intervalIntegrable_vortLInf`.  What makes it true is that the strip
regularity is only assumed on the *closed* sub-strips `[0,t]`, `t < T` — so a uniform bound on the
vorticity is available there, and the worst case (`t → T⁻`) is exactly the blow-up. -/
theorem intervalIntegrable_vortLInf {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf B.u) volume 0 t :=
  Work.FTS.Top.Integrable.intervalIntegrable_vortLInf B

namespace BlowupAt





/-- **The `T = 1` instance, routed literally through `Work.StabilityFar.bkm_divergence_at_one`.**
This is the last clause of the challenge statement at the physical blow-up time, in the exact
shape in which `Work.FTS.Top.theorem_1_of_blowupAt` consumes it: the only inputs are the `lower`
field of the interface and `Work.FTS.Top.intervalIntegrable_vortLInf`. -/
theorem bkm_divergence_one {α : ℝ≥0} (B : BlowupAt α 1) :
    Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => B.u y s) x‖)
      (𝓝[<] 1) Filter.atTop := by
  obtain ⟨c, hc, hlow⟩ := B.lower
  exact Work.StabilityFar.bkm_divergence_at_one hc hlow
    (Work.FTS.Top.intervalIntegrable_vortLInf B)

end BlowupAt

end Work.FTS.Top
end
-- ===== merged: Submission.Work.SolutionDelivery.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}






end Work.SolutionDelivery
end
end
