import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.WindowDefs

/-!
# The hypotheses packages used by the regularity proof of `TW2`

This file only fixes the *shape* of the two uniform (in the perturbation `h`) estimates on the
transition window that the regularity proof of `Work.OddVolterra.Window.TW2` consumes:

* `Window.KvecMStateData n M C` — uniform bound `C` and state-Lipschitz `M` of the manifest odd
  Abel kernel vector `KernelExt.KvecM` and of its first-slot derivative, on the square
  `a, σ ∈ [wLeft, wRight]` (both orders of the two slope slots) and for states in the ball of
  radius `9/20` around the base state;
* `Window.ThetaMStateData n M B` — uniform bound `B` and state-Lipschitz `M` of the manifest odd
  `Θ`-data `KernelExt.ThetaM` on the same region.

Both are purely existential-free `Prop`s, so the two estimates can be proved independently and
combined afterwards.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-- The uniform (in `h`) bound and state-Lipschitz data of the manifest Abel kernel vector
`KernelExt.KvecM` on the transition window, including the first-slot derivative. -/
def KvecMStateData (n : ℕ) (M C : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
    ∀ a ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
    ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
    ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C ∧
      ‖KernelExt.KvecM n h a σ (z 0) (z 1) (z 2) (z 3) -
        KernelExt.KvecM n h a σ (z' 0) (z' 1) (z' 2) (z' 3)‖ ≤ M * ‖z - z'‖ ∧
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a‖ ≤ C ∧
      ‖deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) a -
        deriv (fun u : ℝ => KernelExt.KvecM n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) a‖
        ≤ M * ‖z - z'‖

/-- The uniform (in `h`) bound and state-Lipschitz data of the manifest odd `Θ`-datum
`KernelExt.ThetaM` on the transition window. -/
def ThetaMStateData (n : ℕ) (M B : ℝ) : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
    ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
    ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖KernelExt.ThetaM n h s σ z‖ ≤ B ∧
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
        ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z'‖ ≤ M * ‖z - z'‖

end

end Work.OddVolterra.Window
