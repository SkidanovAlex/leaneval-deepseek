import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs

namespace Work.WilG1.Cell.Junk

theorem contDiffOn_jet_of_coord {n m : ℕ} {V : Set (Fin n → ℝ)}
    (v : Fin n → (Fin n → ℝ) → ℝ) (hv : ∀ i : Fin n, ContDiffOn ℝ m (v i) V) :
    ContDiffOn ℝ m (fun y => jet (fun i => v i y)) V := by
  have h : ∀ i : Fin n, ContDiffOn ℝ m
      (fun y => (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℝ
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) (v i y)) V := by
    intro i
    exact (ContinuousLinearMap.contDiff (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℝ
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))).comp_contDiffOn (hv i)
  refine (ContDiffOn.sum (s := Finset.univ) (fun i _ => h i)).congr ?_
  intro y hy
  simp [jet, ContinuousLinearMap.smulRightL_apply_apply]

end Work.WilG1.Cell.Junk
