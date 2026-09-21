import Mathlib
import Submission.Work.OddVolterra.Existence.window_deriv_close_core

/-!
# The `s`-derivative of the clamped state datum: window `[1/4, 19/20]`

`Work.OddVolterra.Existence.WDC.gscl_data` proves the closeness/Lipschitz bounds for the
`s`-derivative `GsCl` of the clamped state datum on the *narrow* slope window `[7/10, 19/20]`.
Its proof, however, only ever uses the wide window `[1/4, 19/20] = [WinData.wLo, WinData.wHi]`:
the three ingredients (`DiagClose.diagForm_component_estimates`, `WDC.gsCl_eq_diagForm`,
`WDC.differentiableAt_diagForm_slice`) are all stated on the wide window.  This file therefore
restates the lemma on the wide window, with the same proof.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra.Existence.WDC

noncomputable section

/-- **`GsCl`-closeness on the wide window `[1/4, 19/20]`.** -/
theorem w_gscl_data (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (9 / 20),
      (‖Work.OddVolterra.Existence.GsCl n h s z - Work.OddVolterra.Existence.GsCl n 0 s z‖
          ≤ C * δ ∧
       ‖Work.OddVolterra.Existence.GsCl n h s z - Work.OddVolterra.Existence.GsCl n h s z'‖
          ≤ C * dist z z') := by
  obtain ⟨C0, hC00, hC0⟩ := Work.OddVolterra.Existence.DiagClose.diagForm_component_estimates n hn
  refine ⟨C0, hC00, ?_⟩
  intro h δ hh hδ hδ1 hsupp hjet s hs z hz z' hz'
  have hδnn : 0 ≤ δ := hδ.le
  have hs14 : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := hs
  have hsW : s ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi := hs14
  have h2_100 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k hk x) hδ1
  have h2_100_0 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ 1 / 100 := by
    intro k hk x
    rw [iteratedDeriv_zero_fun_wdc]; norm_num
  have hg1 : Work.OddVolterra.Existence.GsCl n h s z =
      deriv (fun u : ℝ => Work.OddVolterra.WinData.diagForm n h u z) s :=
    gsCl_eq_diagForm n hn hh hsupp h2_100 hsW hz
  have hg0 : Work.OddVolterra.Existence.GsCl n 0 s z =
      deriv (fun u : ℝ => Work.OddVolterra.WinData.diagForm n 0 u z) s :=
    gsCl_eq_diagForm n hn contDiff_const support_zero_wdc h2_100_0 hsW hz
  have hgz : Work.OddVolterra.Existence.GsCl n h s z' =
      deriv (fun u : ℝ => Work.OddVolterra.WinData.diagForm n h u z') s :=
    gsCl_eq_diagForm n hn hh hsupp h2_100 hsW hz'
  have hd1 : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.WinData.diagForm n h u z) s :=
    differentiableAt_diagForm_slice n hh hδ1 hjet hs14 hz
  have hd0 : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.WinData.diagForm n 0 u z) s :=
    differentiableAt_diagForm_slice n contDiff_const hδ1 (hjet_zero_wdc hδnn) hs14 hz
  have hdz : DifferentiableAt ℝ (fun u : ℝ => Work.OddVolterra.WinData.diagForm n h u z') s :=
    differentiableAt_diagForm_slice n hh hδ1 hjet hs14 hz'
  refine ⟨?_, ?_⟩
  · rw [hg1, hg0, deriv_pi (differentiableAt_pi.mp hd1), deriv_pi (differentiableAt_pi.mp hd0),
      pi_norm_le_iff_of_nonneg (mul_nonneg hC00 hδnn)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (hC0 h δ hh hδ hδ1 hjet s hs14 z hz z' hz' i).2.1
  · rw [hg1, hgz, deriv_pi (differentiableAt_pi.mp hd1), deriv_pi (differentiableAt_pi.mp hdz),
      pi_norm_le_iff_of_nonneg (mul_nonneg hC00 dist_nonneg)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (hC0 h δ hh hδ hδ1 hjet s hs14 z hz z' hz' i).2.2

end

end Work.OddCurveB.Step2
