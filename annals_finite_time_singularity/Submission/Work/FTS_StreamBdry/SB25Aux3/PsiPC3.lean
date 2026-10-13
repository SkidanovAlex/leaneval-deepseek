import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.psiP_c3`

The `U`-slot part `P := psiP αG Ψ` of a `C³` stream function is itself `C³` on the open quadrant.

This is `SB3.psiP_c2` with `2` replaced by `3`: SB1′ writes `Ψ = P + κ · gaugeMode` on `Qd`
(`SB1.sb1_gauge_of_parts`), the gauge mode is analytic (`SB25.contDiffOn_uncurry_gaugeMode`), and
`h3` is exactly the `C³` hypothesis on `Ψ`, so the difference `Ψ - κ·gaugeMode` (which agrees with
`P`) is `C³` on `Qd`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux3

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

/-- `psiP αG Ψ` is `C³` on the open quadrant whenever `Ψ` is. -/
theorem psiP_c3 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hg : ContDiffOn ℝ 3 (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (gaugeMode αG) p)
      Work.Construction.Qd :=
    h3.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

end Work.FTS_StreamBdry.SB25Aux3
