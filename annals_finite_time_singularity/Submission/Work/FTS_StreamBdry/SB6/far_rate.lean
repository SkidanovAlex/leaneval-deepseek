import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.sb5_compare
import Submission.Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB25.dq1_facts
import Submission.Work.FTS_StreamBdry.SB25.dq2_facts
import Submission.Work.FTS_StreamBdry.SB25.bslOp_dilate
import Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd
import Submission.Work.FTS_StreamBdry.SB5.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB6

theorem far_rate {αG M L Mf K2 : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hth2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K2)
    (hdec : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) Filter.atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j : ℕ, j ≤ 2 →
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ K * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by
  obtain ⟨hL, hF0⟩ := hF.2.2.2.2
  -- the two `θ`-constants: `∂_θ psiP` is bounded by `3M` (SB5 `abs_pth_psiP_le`), and
  -- `∂_θ² psiP` is the hypothesis `hth2`
  set K : ℝ := max (3 * M) K2 with hKdef
  have hK1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K :=
    fun z θ hzθ =>
      (Work.FTS_StreamBdry.SB5.abs_pth_psiP_le hαG h3 hslot z θ hzθ).trans (le_max_left _ _)
  have hK2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ K :=
    fun z θ hzθ => (hth2 z θ hzθ).trans (le_max_right _ _)
  -- the core Phragmén–Lindelöf / maximum-principle decay, with the barrier `sb5_barrier_proved`
  have hcore := Work.FTS_StreamBdry.SB5.sb5_decay_core
    (P := Work.FTS.StreamBdryIface.psiP αG Ψ) (F := F) (K := K)
    hαG hL (Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot)
    (Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot) hF0
    (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot) hK1 hK2
    (Work.FTS_StreamBdry.SB5.tendsto_psiP_atTop hαG hsol h3 hslot)
    Work.FTS_StreamBdry.sb5_barrier_proved
  -- the constant of the core decay need not be positive; `max M 1` is, and only increases it
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro z θ hzθ hLz j hj
  have hz : 0 < z := Work.FTS_StreamBdry.Qd_pos hzθ
  have hnn : 0 ≤ Work.Construction.s2 θ * (L / z) ^ (4 / αG) :=
    mul_nonneg (le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hzθ))
      (le_of_lt (Real.rpow_pos_of_pos (div_pos hL hz) _))
  calc |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := hcore z θ hzθ hLz j hj
    _ = M * (Work.Construction.s2 θ * (L / z) ^ (4 / αG)) := by ring
    _ ≤ max M 1 * (Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ = max M 1 * Work.Construction.s2 θ * (L / z) ^ (4 / αG) := by ring

end Work.FTS_StreamBdry.SB6
