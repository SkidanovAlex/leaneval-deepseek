import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma

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

/-- The `θ`-slice of `D_z(∂_θ D_z^r V)` at any `z ∈ [0,∞)` is dominated by a multiple of
the integrable angular weight `sin(2θ)^{-η}`: it is continuous on the compact interval
`Iθ` (because `V` is smooth on an open neighbourhood of the closed quadrant and both
`∂_θ` and `D_z` preserve this class), hence bounded. -/
theorem slice_z_integrable {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (r : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  intro z hz
  have hsm' : Work.Spaces.SmoothNbhd
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V))) :=
    ((Work.Spaces.smoothNbhd_DzIter hsm r).pth).Dz
  exact Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta
    (continuousOn_slice_of_smoothNbhd hsm' hz)

end Work.FTS.EllipticEst.RPFresh
