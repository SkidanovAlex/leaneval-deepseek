import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3

theorem psiP_c2 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ))
      Work.Construction.Qd := by
  -- SB1′: on the open quadrant, `Ψ = psiP αG Ψ + κ · gaugeMode αG`
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  -- `Ψ` is `C²` and the gauge mode is analytic on `Qd`, so their difference is `C²`
  have hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
    h3.of_le (by norm_num)
  have hg : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG) p)
      Work.Construction.Qd :=
    hΨ.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

end Work.FTS_StreamBdry.SB3
