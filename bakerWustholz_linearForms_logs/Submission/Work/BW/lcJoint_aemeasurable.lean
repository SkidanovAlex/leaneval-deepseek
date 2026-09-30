import Mathlib
import Submission.Work.BW.lcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped ENNReal
open MeasureTheory Set

theorem lcJoint_aemeasurable {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) (hcl : IsClosed C) (s : ℝ) :
    AEMeasurable (Function.uncurry (Work.BW.lcJoint C k h s))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) := by
  apply Measurable.aemeasurable
  have hA : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator ((hcl.preimage (continuous_insertNth k s)).measurableSet)).comp
      measurable_fst
  have hB : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∏ i, lcInd (h i (p.1 i)) (p.2 i)) := by
    apply Finset.measurable_prod
    intro i _
    exact measurable_lcInd.comp
      (((hh_meas i).comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  rw [show Function.uncurry (Work.BW.lcJoint C k h s) = fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) p.1)
        * ∏ i, lcInd (h i (p.1 i)) (p.2 i) from by funext p; rfl]
  exact hA.mul hB

end Work.BW
