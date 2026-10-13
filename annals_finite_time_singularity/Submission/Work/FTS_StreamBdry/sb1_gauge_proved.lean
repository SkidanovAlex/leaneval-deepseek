import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb1_gauge_proved` — the frozen SB1′ producer `StreamBdryIface.sb1_gauge`

Every `C³` stream function on the open quadrant whose `U`-slot is bounded (`SlotBd`) differs from
the particular solution `psiP` by a multiple of the gauge mode `gaugeMode αG = z^{-3/αG}/cos θ`.
No growth hypothesis is needed (FIX-A): the constant of integration is pinned by the boundedness of
`V(psiP)` at `z → 0⁺` (`SB1.psiP_Vop_bnd`), which is what makes the `θ`-ODE `c' = tan θ·c` hold.

Assembled in `SB1/Engine.lean` (`SB1.sb1_gauge_of_parts`) from the three engine lemmas
`SB1.psiP_ode`, `SB1.psiP_diff`, `SB1.psiP_Vop_bnd`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd gaugeMode psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB1′ proved** (frozen type `sb1_gauge`): the gauge decomposition, with no growth hypothesis. -/
theorem sb1_gauge_proved {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Ψ z θ = psiP αG Ψ z θ + κ * gaugeMode αG z θ :=
  SB1.sb1_gauge_of_parts hαG h3 hslot (SB1.psiP_ode hαG h3 hslot)
    (SB1.psiP_diff hαG h3 hslot) (SB1.psiP_Vop_bnd hαG h3 hslot)

end Work.FTS_StreamBdry
