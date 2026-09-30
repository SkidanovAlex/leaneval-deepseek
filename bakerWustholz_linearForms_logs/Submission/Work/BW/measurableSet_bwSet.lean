import Mathlib
import Submission.Work.BW.lcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set

/-- For a fixed coordinate index `i`, the map `z ↦ h i (z (k.succAbove i))` is measurable,
being the composition of the measurable function `h i` with the (continuous) coordinate
projection. -/
lemma measurable_h_comp_succAbove {n : ℕ} (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (i : Fin n) :
    Measurable (fun z : Fin (n+1) → ℝ => h i (z (k.succAbove i))) :=
  (hh_meas i).comp (continuous_apply (k.succAbove i)).measurable

/-- For a fixed coordinate index `i`, the set `{z | u i ≤ h i (z (k.succAbove i))}` is
measurable. -/
lemma measurableSet_bwSet_iInter {n : ℕ} (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (u : Fin n → ℝ) :
    MeasurableSet (⋂ i, {z : Fin (n+1) → ℝ | u i ≤ h i (z (k.succAbove i))}) :=
  MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const (measurable_h_comp_succAbove k h hh_meas i)

theorem measurableSet_bwSet {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) (hcl : IsClosed C) (u : Fin n → ℝ) :
    MeasurableSet (Work.BW.bwSet C k h u) := by
  by_cases hu : ∀ i, 0 ≤ u i
  · rw [bwSet_of_forall_nonneg _ _ _ hu]
    exact hcl.measurableSet.inter (measurableSet_bwSet_iInter k h hh_meas u)
  · rw [bwSet_of_not _ _ _ hu]
    exact MeasurableSet.empty

end Work.BW
