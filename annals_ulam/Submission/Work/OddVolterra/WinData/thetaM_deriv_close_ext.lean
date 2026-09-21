import Mathlib
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.WinData.deriv2_main
import Submission.Work.OddVolterra.WinData.deriv2_hkv

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

theorem thetaM_deriv_close_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
      (‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n 0 u σ z) s‖ ≤ C * δ ∧
        ‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z') s‖ ≤ L * ‖z - z'‖) :=
  thetaM_deriv_close_of_KvecM n hn (KvecM_deriv2_ext n hn)

end

end Work.OddVolterra.WinData
