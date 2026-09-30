import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Matrix

lemma psdDiagZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {i : ι} (hi : A i i = 0) :
    ∀ j, A i j = 0 := by
  -- A positive semidefinite matrix `M` with `M i i = 0` has vanishing `i`-th column.
  have hcol : ∀ (M : Matrix ι ι ℝ), M.PosSemidef → M i i = 0 →
      M *ᵥ Pi.single i (1 : ℝ) = 0 := by
    intro M hM hMii
    rw [← hM.dotProduct_mulVec_zero_iff]
    simp [hMii]
  intro j
  -- Apply the column statement to the transpose, whose `i`-th column is the `i`-th row of `A`.
  have h0 := congrFun (hcol Aᵀ hA.transpose (by simpa using hi)) j
  simpa using h0

end Work.BW
