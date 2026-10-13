import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceWeightedL2
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceZeroOfConv
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMemAe
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsTraceTransfer
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsTraceTransferPi
import Submission.Work.FTS.StrongEps.EpsLocalPStar.RhoMargProps
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ConvInjective
import Submission.Work.FTS.StrongEps.EpsLocalPStar.FourierZeroNull
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTraceO
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePiO
import Submission.Work.FTS.StrongEps.EpsLocalPStar.PzJepsEndpointTrace
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceAt0_of_SmoothOpen_HkMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceAtPi_of_SmoothOpen_HkMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_Pi
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem EpsMemOfClassCJeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ δ : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen δ → Work.Spaces.HkMem α 6 δ →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ)) →
        Work.FTS.StrongEps.EpsMem α δ ∧
          Work.FTS.StrongEps.EpsSq α δ
            ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 δ := by
  obtain ⟨C, hCpos, hCS⟩ := TraceToEpsMemAe
  refine ⟨C, hCpos, ?_⟩
  intro α hα ε hε hε1 δ hso hm hg
  -- the endpoint traces of the mollified profile `J_ε δ` vanish
  obtain ⟨hj0, hjpi⟩ := PzJepsEndpointTrace hα.1 hg
  -- `HkMem α 1 δ` (the slot level actually used by the traces)
  have hm1 : Work.Spaces.HkMem α 1 δ := Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hm
  -- the angular traces of `δ` at both endpoints
  obtain ⟨lam0, hlam0m, htr0, hbd0, hint0⟩ := TraceAt0_of_SmoothOpen_HkMem hα hso hm1
  obtain ⟨lamp, hlampm, htrp, hbdp, hintp⟩ := TraceAtPi_of_SmoothOpen_HkMem hα hso hm1
  -- the convolution equations for the two traces
  have hconv0 := JepsMarginalZero_zero hα hρ hε hso hm1 hlam0m hint0 htr0 hbd0 hj0
  have hconvp := JepsMarginalZero_Pi hα hρ hε hso hm1 hlampm hintp htrp hbdp hjpi
  -- Fourier injectivity: both traces vanish a.e.
  have hz0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), lam0 z = 0 :=
    TraceZeroOfConv ρ hρ.moll hε hε1 hint0 hlam0m hconv0
  have hzp : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), lamp z = 0 :=
    TraceZeroOfConv ρ hρ.moll hε hε1 hintp hlampm hconvp
  -- hence the traces of `δ` itself vanish a.e.
  have ht0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      Filter.Tendsto (fun θ => δ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [htr0, hz0] with z h1 h2
    rw [h2] at h1
    exact h1
  have htp : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      Filter.Tendsto (fun θ => δ z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    filter_upwards [htrp, hzp] with z h1 h2
    rw [h2] at h1
    exact h1
  exact hCS α hα δ hso hm1 ht0 htp

end Work.FTS.StrongEps.EpsLocalPStar
