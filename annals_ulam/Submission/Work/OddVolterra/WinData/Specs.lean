import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# The estimate interfaces of the odd-case window construction

These `Prop`s collect the estimates that the window construction of
`Work.OddVolterra.Existence.odd_volterra_window_solution` consumes, so that the engine part can be
stated and proved independently of the estimates.

* `ThetaMCloseBox n a b ρ` — closeness in `h` of the manifest kernel `𝚯M` on `[a,b]²` and on the
  state ball of radius `ρ` around `baseState σ` (the crux estimate);
* `FderivGoddCloseBox n a b ρ` — closeness in `h` of `fderiv (Godd n h s ·)` to the unperturbed
  linearization at `baseState s`, on the state ball of radius `ρ`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-- Closeness of the manifest kernel `𝚯M` in the perturbation, on a slope box and on a state
ball. -/
def ThetaMCloseBox (n : ℕ) (a b ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
    ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      ∀ z ∈ Metric.closedBall (baseState σ) ρ,
      ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z‖ ≤ C * δ

/-- Closeness of the linearization of the state datum in the perturbation, on a slope box and on
a state ball. -/
def FderivGoddCloseBox (n : ℕ) (a b ρ : ℝ) : Prop :=
  ∃ Cg : ℝ, 0 < Cg ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
    Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
    ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (baseState s) ρ,
      ‖fderiv ℝ (fun w => Godd n h s w) z -
        fderiv ℝ (fun w => Godd n 0 s w) (baseState s)‖
        ≤ Cg * ‖z - baseState s‖ + Cg * δ

end

end Work.OddVolterra.WinData
