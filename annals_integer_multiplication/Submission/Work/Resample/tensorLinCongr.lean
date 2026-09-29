import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.tensorComp

namespace Work.Resample

open HvdH

/-- `digitProd` is insensitive to replacing `f` by a `g` agreeing in the relevant range. -/
theorem digitProd_congr {ss ts : List ℕ} {f g : ℕ → ℕ → ℕ → ℂ}
    (h : ∀ i < ss.length, ∀ j k, f i j k = g i j k) (J K : ℕ) :
    digitProd ss ts f J K = digitProd ss ts g J K := by
  unfold digitProd
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi) _ _

theorem tensorLinCongr {ss ts : List ℕ} {f g : ℕ → ℕ → ℕ → ℂ}
    (h : ∀ i < ss.length, ∀ j k, f i j k = g i j k) (u : Fin ss.prod → ℂ) :
    Work.Resample.tensorLin ss ts f u = Work.Resample.tensorLin ss ts g u := by
  simp only [tensorLin_apply]
  funext J
  apply Finset.sum_congr rfl
  intro K _
  rw [digitProd_congr h (J : ℕ) (K : ℕ)]

end Work.Resample
