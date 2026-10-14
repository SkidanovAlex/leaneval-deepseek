import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.InterpTrunc.fourInt_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## Smoothness of the truncated function on the strip -/


/-! ## Vanishing of the derivatives off the support in `z` -/




/-! ## Integrability of the outer weighted square integral -/


/-! ## The four integrability conditions of the truncated function -/


end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.Blocks.InterpTrunc.mixInt_Icc_le_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false



end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.Blocks.InterpTrunc.sliceL2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false




end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.Blocks.InterpTrunc.sliceSplit2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false



end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.Blocks.InterpTrunc.sliceSplit3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false



end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.slice_z_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

open scoped Real Topology
open MeasureTheory Set Filter

/-- The angular slice `θ ↦ h z θ` of a function which is smooth on an open neighbourhood
of the closed quadrant is continuous on `Iθ`, for every `z ∈ Iz`. -/
theorem continuousOn_slice_of_smoothNbhd {h : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd h)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : ContinuousOn (fun θ => h z θ) Work.Spaces.Iθ := by
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry h) (z, θ) :=
    hsm.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  have hcont : ContinuousAt (fun θ' : ℝ => Function.uncurry h (z, θ')) θ :=
    hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt
  exact hcont.continuousWithinAt


end Work.FTS.EllipticEst.RPFresh
end
