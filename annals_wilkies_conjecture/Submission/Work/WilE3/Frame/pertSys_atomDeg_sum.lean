import Mathlib
import Submission.Work.WilE3.Frame.CutSys

namespace Work.WilE3.Frame

theorem pertSys_atomDeg_sum {k r j : ℕ} (hjk : j < k) :
    (∑ i : Fin k, WilkiesDesign.E.atomDeg
      (Work.WilE3.Frame.pertSys (k := k) (r := r) hjk i)) = k := by
  have h1 : ∀ i : Fin k, WilkiesDesign.E.atomDeg
      (Work.WilE3.Frame.pertSys (k := k) (r := r) hjk i) = 1 := by
    intro i
    by_cases hi : i = rowF hjk
    · subst hi
      rw [pertSys_rowF, WilkiesDesign.E.atomDeg, MvPolynomial.totalDegree_C]
    · rw [pertSys_of_ne hjk hi, WilkiesDesign.E.atomDeg, MvPolynomial.totalDegree_zero]
  calc (∑ i : Fin k, WilkiesDesign.E.atomDeg
        (Work.WilE3.Frame.pertSys (k := k) (r := r) hjk i))
      = ∑ _i : Fin k, (1 : ℕ) := Finset.sum_congr rfl fun i _ => h1 i
    _ = k := by simp

end Work.WilE3.Frame
