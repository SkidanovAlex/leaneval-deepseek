import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.WinData.Specs
import Submission.Work.OddVolterra.WinData.LowClamp
import Submission.Work.OddVolterra.WinData.manifest_locality_low
import Submission.Work.OddVolterra.WinData.frozen_tail_close_low
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.Window.volterra_unique
import Submission.Work.OddCurveB.Est.exists_linearization
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.WinData.lc_low_aux

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology Interval

theorem lc_low_piece (n : ℕ) (hn : 1 ≤ n) (ν : ℝ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 100)
    (hL1 : Work.OddVolterra.WinData.ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ))
    (hL4 : Work.OddVolterra.WinData.FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100 ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η₀ → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∀ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, dist (Z s) (Work.OddVolterra.baseState s) ≤ θ) →
        ∃ ZL : ℝ → Work.OddVolterra.St,
          ContinuousOn ZL (Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ)) ∧
          (∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ),
            Work.OddVolterra.Godd n h s (ZL s) =
              (∫ σ in s..(7 / 10 : ℝ), Work.OddVolterra.Theta n h s σ (ZL σ)) +
                (∫ σ in (7 / 10 : ℝ)..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
                Work.OddVolterra.Xi n h s) ∧
          (∀ s ∈ Set.Icc (1 / 4 : ℝ) (7 / 10 : ℝ),
            dist (ZL s) (Work.OddVolterra.baseState s) ≤ ν) :=
  lc_low_piece_aux n hn ν hν hν2 hL1 hL4

end Work.OddVolterra.WinData
