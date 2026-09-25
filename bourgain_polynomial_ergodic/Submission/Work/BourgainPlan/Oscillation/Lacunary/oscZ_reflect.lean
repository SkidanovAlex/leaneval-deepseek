import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

/-!
# Reflection invariance of the `ℤ`-side block-oscillation functional

The counting measure on `ℤ` is invariant under the reflection `y ↦ -y`, hence so is the
`ℤ`-side oscillation functional `oscZ`: replacing the family `A i ·` by its reflection
`A i (-·)` leaves `Σ_{j<J} ∫_ℤ (sup_{k_j ≤ i < k_{j+1}} |A_i - A_{k_j}|)²` unchanged.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-- `∫_ℤ f(-x) dcount = ∫_ℤ f(x) dcount`: counting measure on `ℤ` is invariant under `y ↦ -y`. -/
lemma lintegral_count_neg (f : ℤ → ℝ≥0∞) :
    ∫⁻ x : ℤ, f (-x) ∂Measure.count = ∫⁻ x : ℤ, f x ∂Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact (Equiv.neg ℤ).tsum_eq f

theorem oscZ_reflect (A : ℕ → ℤ → ℂ) (J : ℕ) (k : ℕ → ℕ) :
    Work.BourgainPlan.Oscillation.oscZ (fun i y => A i (-y)) J k
      = Work.BourgainPlan.Oscillation.oscZ A J k := by
  simp only [Work.BourgainPlan.Oscillation.oscZ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := lintegral_count_neg (fun y : ℤ =>
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i y - A (k j) y‖ₑ) ^ (2 : ℝ))
  simpa using this

end Work.BourgainPlan.Oscillation.Lacunary
