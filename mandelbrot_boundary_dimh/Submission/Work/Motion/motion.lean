import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding
import Submission.Work.Motion.Holder
import Submission.Work.Motion.exists_pertData
import Submission.Work.Motion.exists_sep
import Submission.Work.Motion.coding_lipschitz
import Submission.Work.Motion.coding_holomorphic
import Submission.Work.Motion.coding_bounded
import Submission.Work.Motion.coding_holder

/-!
# AREA MOTION — the holomorphic motion of a dynamical IFS

Assembles the target `MotionStatement` from the components:
`exists_pertData` (moving inverse branches), `Coding.lean` (coding map, equivariance, uniform
contraction, agreement with `codingPt`), `exists_sep` (separation of level-1 pieces),
`coding_injective` (injectivity), `coding_holomorphic`, `coding_lipschitz`, `coding_bounded` and
`coding_holder` (Hölder dependence on the parameter).
-/

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter
open scoped Topology

theorem motion : MotionStatement := by
  intro c₀ N τ n p r K hN hIFS hDyn a ha
  have hN1 : 1 ≤ N := by omega
  obtain ⟨D⟩ := exists_pertData hN hIFS hDyn
  obtain ⟨ρ_s, hρ_s_pos, hρ_s_le, g, hg, hsep⟩ := exists_sep hN1 hIFS D
  obtain ⟨ρ_h, hρ_h_pos, hρ_h_le, C_h, hC_h, hholder⟩ := coding_holder hN1 hIFS D a ha
  obtain ⟨L, hL0, hlips⟩ := coding_lipschitz D
  obtain ⟨B, hB⟩ := coding_bounded hN1 D
  set ρ : ℝ := min D.ρ (min ρ_s ρ_h) with hρdef
  have hρ_pos : 0 < ρ := lt_min D.hρ (lt_min hρ_s_pos hρ_h_pos)
  have hρD : ρ ≤ D.ρ := min_le_left _ _
  have hρ_s : ρ ≤ ρ_s := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_h : ρ ≤ ρ_h := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρ_pos, (fun c ω => D.coding c ω), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact PertData.coding_c₀ D ω
  · intro ω
    exact (coding_holomorphic D ω).mono (ball_subset_ball hρD)
  · intro c hc
    exact PertData.coding_injective D hρD hρ_s hg hsep hc
  · intro c hc ω
    exact PertData.coding_equivar D c (ball_subset_ball hρD hc) ω
  · exact ⟨B, fun c hc ω j => hB c (ball_subset_ball hρD hc) ω j⟩
  · refine ⟨2 * D.s / ((1 + D.θ) / 2), (1 + D.θ) / 2, ?_, ?_, ?_⟩
    · linarith [D.hθ0]
    · linarith [D.hθ1]
    · intro c hc k ω ω' h
      exact PertData.coding_contract D c (ball_subset_ball hρD hc) h
  · exact ⟨L, fun c hc c' hc' ω =>
      hlips c (ball_subset_ball hρD hc) c' (ball_subset_ball hρD hc') ω⟩
  · exact ⟨C_h, fun c hc c' hc' ω ω' =>
      hholder c (ball_subset_ball hρ_h hc) c' (ball_subset_ball hρ_h hc') ω ω'⟩

end Work.Motion
