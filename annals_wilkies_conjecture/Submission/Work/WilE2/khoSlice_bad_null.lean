import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.slice_null_ae
import Submission.Work.WilE2.sard_square

namespace Work.WilE2

theorem khoSlice_bad_null {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (hΨ : ∀ z : Fin (n + 1) → ℝ, HasFDerivAt (rolleMap S F) (fderiv ℝ (rolleMap S F) z) z) :
    MeasureTheory.volume {y : Fin n → ℝ | ¬ KhoSliceNull S F y} = 0 := by
  -- Sard's lemma (square case) for `rolleMap S F` says that the image of the critical set
  -- `{z | det (fderiv (rolleMap S F) z) = 0}` is Lebesgue-null.
  have hN : MeasureTheory.volume
      (rolleMap S F '' {z : Fin (n + 1) → ℝ | (fderiv ℝ (rolleMap S F) z).det = 0}) = 0 :=
    sard_square (rolleMap S F) (fderiv ℝ (rolleMap S F)) hΨ
  -- Fubini for the decomposition `(y, t) ↦ Fin.snoc y t`: almost every slice of that null set
  -- is null, which is exactly the assertion.
  have h := slice_null_ae hN
  simpa only [KhoSliceNull, ne_eq] using h

end Work.WilE2
