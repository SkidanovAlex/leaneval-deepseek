import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB5.PthIter2Reproved
import Submission.Work.FTS_StreamBdry.SB25.sb5_compare
import Submission.Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs
import Submission.Work.FTS_StreamBdry.SB25.bslOp_dilate
import Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd
import Submission.Work.FTS_StreamBdry.SB25.dq1_facts
import Submission.Work.FTS_StreamBdry.SB25.dq2_facts
import Submission.Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved
import Submission.Work.FTS_StreamBdry.SB5.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.sb5_decay` — decay of the `U`-slot part outside the support

The producer `sb5_decay`, assembled from `SB5.Core.sb5_decay_core` (Phragmén–Lindelöf comparison
for the ground-state operator and dilate difference quotients) and the SB3 bounds.
See `Submission/Work/FTS_StreamBdry/SB5/Prep.lean`, `Ang.lean`, `Core.lean` for the helpers.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## §11 The producer -/

theorem sb5_decay {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hbar : Work.FTS.StreamBdryIface.SB5Barrier) :
    ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ K * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
  obtain ⟨hL, hF0⟩ := hF.2.2.2.2
  obtain ⟨K₂, hK₂⟩ := Work.FTS_StreamBdry.SB3.pthIter2_le_reproved hαG hsol h3 hslot hF
  refine ⟨M, Work.FTS_StreamBdry.SB5.sb5_decay_core (P := Work.FTS.StreamBdryIface.psiP αG Ψ)
    (F := F) hαG hL (Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot)
    (Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot) hF0
    (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot)
    (fun z θ hzθ => (abs_pth_psiP_le hαG h3 hslot z θ hzθ).trans (le_max_left _ _))
    (fun z θ hzθ => (hK₂ z θ hzθ 0 (by norm_num)).trans (le_max_right _ _))
    (tendsto_psiP_atTop hαG hsol h3 hslot) hbar⟩

