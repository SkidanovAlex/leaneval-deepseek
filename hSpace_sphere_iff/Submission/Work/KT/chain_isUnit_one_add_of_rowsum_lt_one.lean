import Mathlib
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one

namespace Work.KT

/-- If the row-sum norm of a complex matrix `B` is `< 1` then `1 + B` is a unit. -/
theorem chain_isUnit_one_add_of_rowsum_lt_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : (Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ : NNReal) < 1) : IsUnit (1 + B) := by
  have hA : (Finset.univ.sup fun i => ∑ j, ‖(-B) i j‖₊ : NNReal) < 1 := by
    simpa using hB
  have h := isUnit_one_sub_of_matNorm_lt_one (-B) hA
  simpa using h

end Work.KT
