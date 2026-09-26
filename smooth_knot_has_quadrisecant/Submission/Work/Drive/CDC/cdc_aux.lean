import Mathlib
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmDefs

/-!
# Auxiliary estimates for the "drive" lemmas of the chart data

The two "drive" lemmas `Work.Drive.CDC.cdc_endpointChart` and `Work.Drive.CDC.cdc_profile` reduce the
clauses of `Work.Drive.Generic.nclmDataC` to a handful of estimates on the retained arc in the
needle's chart.  This module collects the *sharpened* window comparison that those estimates need:
unlike `Work.Drive.Generic.nclm_window_eps`, whose tolerance is the fixed factor `2`, the estimates
of the height profile compare the width `sweepW' D σ` at a *target* parameter `σ` of the blur window
with the reference width `sweepW' D ε`, and the comparison must be sharp — a factor `2` is too much
(it would spoil the factor `2` of the bound `|H̃| ≤ 2 ‖chartUp‖`).
-/

noncomputable section
namespace Work.Drive.CDC

open LeanEval.KnotTheory.Quadrisecant

/-- **The sharpened window comparison at scale `ε`.**  For every relative tolerance `η > 0` there is
a window radius `Λ > 0` such that, for every `δ₂ ∈ (0, Λ]` and every `σ` with
`ε - δ₂ ≤ σ ≤ ε + δ₂`, the width `sweepW' D ·` and the two branch lifts `taR D ·`, `tbR D ·` have
moved from their values at `ε` by at most `η` times the reference width `sweepW' D ε`.

This is `Work.Drive.Generic.nclm_window_eps` with the fixed tolerances `1/2` (width) and `1/8`
(lifts) replaced by an arbitrary relative tolerance `η`; the proof is the same continuity argument
(the functions are continuous at `ε` and `sweepW' D ε > 0`). -/
theorem cdc_window_sharp {d : BandArcData} (D : Work.Drive.SweepData d) {ε η : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) :
    ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧
      ∀ δ₂ σ : ℝ, 0 < δ₂ → δ₂ ≤ Λ → ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        |Work.Drive.sweepW' D σ - Work.Drive.sweepW' D ε| ≤ η * Work.Drive.sweepW' D ε ∧
        |Work.Drive.taR D σ - Work.Drive.taR D ε| ≤ η * Work.Drive.sweepW' D ε ∧
        |Work.Drive.tbR D σ - Work.Drive.tbR D ε| ≤ η * Work.Drive.sweepW' D ε := by
  have hWpos : 0 < Work.Drive.sweepW' D ε :=
    Work.Drive.wds_sweepW'_pos D hε0 hε1
  have ht : 0 < η * Work.Drive.sweepW' D ε := mul_pos hη hWpos
  obtain ⟨θa, hθa, ha⟩ := Metric.continuousAt_iff.mp
    ((Work.Drive.arcWin_taR_continuous D).continuousAt (x := ε)) (η * Work.Drive.sweepW' D ε) ht
  obtain ⟨θb, hθb, hb⟩ := Metric.continuousAt_iff.mp
    ((Work.Drive.arcWin_tbR_continuous D).continuousAt (x := ε)) (η * Work.Drive.sweepW' D ε) ht
  obtain ⟨θw, hθw, hw⟩ := Metric.continuousAt_iff.mp
    ((Work.Drive.arcWin_sweepW'_continuous D).continuousAt (x := ε)) (η * Work.Drive.sweepW' D ε) ht
  refine ⟨min (min (min θa θb) θw / 2) (ε / 2), ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  · exact min_le_right _ _
  · intro δ₂ σ hδ₂0 hδ₂Λ hσlo hσhi
    set m : ℝ := min (min θa θb) θw with hmdef
    have hmpos : 0 < m := lt_min (lt_min hθa hθb) hθw
    have hδε : |σ - ε| ≤ δ₂ := abs_le.mpr ⟨by linarith, by linarith⟩
    have hm2 : δ₂ ≤ m / 2 := le_trans hδ₂Λ (min_le_left _ _)
    have hθ : dist σ ε < m := by
      rw [Real.dist_eq]
      have h2 : |σ - ε| ≤ δ₂ := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith [hmpos]
    have hm_le_a : m ≤ θa := by rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hm_le_b : m ≤ θb := by rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm_le_w : m ≤ θw := by rw [hmdef]; exact min_le_right _ _
    have h1 : dist σ ε < θa := lt_of_lt_of_le hθ hm_le_a
    have h2 : dist σ ε < θb := lt_of_lt_of_le hθ hm_le_b
    have h3 : dist σ ε < θw := lt_of_lt_of_le hθ hm_le_w
    have hA := ha h1
    have hB := hb h2
    have hC := hw h3
    rw [Real.dist_eq] at hA hB hC
    exact ⟨le_of_lt hC, le_of_lt hA, le_of_lt hB⟩

end Work.Drive.CDC
