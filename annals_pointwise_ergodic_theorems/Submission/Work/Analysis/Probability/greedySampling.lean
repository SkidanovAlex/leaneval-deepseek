import Mathlib
import Submission.Work.Analysis.Probability.greedyChain

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-! ## The sampled martingale along the greedy chain -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `k`-th greedy time of the process `H` at level `δ`. -/
noncomputable def greedyTimeProc (H : ℕ → Ω → ℝ) (δ : ℝ) (k : ℕ) : Ω → ℕ∞ :=
  fun ω => greedyTime (fun n => H n ω) δ k

/-- The `k`-th greedy time truncated at the horizon `N`. -/
noncomputable def greedyStop (H : ℕ → Ω → ℝ) (δ : ℝ) (N k : ℕ) : Ω → ℕ∞ :=
  fun ω => min (greedyTimeProc H δ k ω) (N : ℕ∞)

/-- The anchor value of `H` at the `k`-th truncated greedy time. -/
noncomputable def greedyAnchor (H : ℕ → Ω → ℝ) (δ : ℝ) (N k : ℕ) : Ω → ℝ :=
  stoppedValue H (greedyStop H δ N k)

theorem isStoppingTime_greedyTimeProc {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {H : ℕ → Ω → ℝ} (hH : MeasureTheory.StronglyAdapted ℱ H) (δ : ℝ) (k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (greedyTimeProc H δ k) :=
  isStoppingTime_greedyTime hH δ k

theorem isStoppingTime_greedyStop {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {H : ℕ → Ω → ℝ} (hH : MeasureTheory.StronglyAdapted ℱ H) (δ : ℝ) (N k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (greedyStop H δ N k) :=
  (isStoppingTime_greedyTimeProc hH δ k).min_const N

theorem greedyAnchor_condExp {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.SigmaFinite μ]
    [MeasureTheory.SigmaFiniteFiltration μ ℱ] {H : ℕ → Ω → ℝ}
    (hH : MeasureTheory.Martingale H ℱ μ) (δ : ℝ) (N k : ℕ) :
    greedyAnchor H δ N k =ᵐ[μ]
      μ[H N | (isStoppingTime_greedyStop hH.stronglyAdapted δ N k).measurableSpace] := by
  haveI hfin : MeasureTheory.SigmaFinite (μ.trim
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N k).measurableSpace_le) :=
    MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N k)
  have h := hH.stoppedValue_ae_eq_condExp_of_le (hτ := isStoppingTime_const ℱ N)
    (hσ := isStoppingTime_greedyStop hH.stronglyAdapted δ N k)
    (fun x => min_le_right _ _) (fun x => le_rfl)
  rw [stoppedValue_const] at h
  exact h

end Work.Analysis.Probability
