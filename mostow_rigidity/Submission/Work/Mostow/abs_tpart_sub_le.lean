import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.absCoshSubCoshLe
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The time coordinate `tpart u = √(1+‖u‖²)` is `sinh 1`-Lipschitz on the ball of radius `1`
around the base point `0`.  This follows from `tpart u = cosh (hdist 0 u)`, the mean value
bound `|cosh a - cosh b| ≤ sinh 1·|a-b|` for `a,b ∈ [0,1]` (`absCoshSubCoshLe`), and the
triangle inequality for `hdist`. -/
theorem abs_tpart_sub_le (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    {u v : Submission.Mostow.E n}
    (hu : Submission.Mostow.hdist (0 : Submission.Mostow.E n) u ≤ 1)
    (hv : Submission.Mostow.hdist (0 : Submission.Mostow.E n) v ≤ 1) :
    |Submission.Mostow.tpart u - Submission.Mostow.tpart v|
      ≤ Real.sinh 1 * Submission.Mostow.hdist u v := by
  have hnn : ∀ x : E n, 0 ≤ hdist (0 : E n) x := fun x => hI.1 0 x
  have hsym : ∀ x y : E n, hdist x y = hdist y x := fun x y => hI.2.1 x y
  have htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z := fun x y z => hI.2.2.2.1 x y z
  -- `|hdist 0 u - hdist 0 v| ≤ hdist u v` (triangle inequality, both directions)
  have hab : |hdist (0 : E n) u - hdist (0 : E n) v| ≤ hdist u v := by
    rw [abs_sub_le_iff]
    constructor
    · have h := htri (0 : E n) v u
      rw [hsym v u] at h
      linarith
    · have h := htri (0 : E n) u v
      linarith
  calc |tpart u - tpart v|
      = |Real.cosh (hdist (0 : E n) u) - Real.cosh (hdist (0 : E n) v)| := by
        rw [cosh_hdist_zero u, cosh_hdist_zero v]
    _ ≤ Real.sinh 1 * |hdist (0 : E n) u - hdist (0 : E n) v| :=
        absCoshSubCoshLe 1 _ _ (hnn u) (hnn v) hu hv
    _ ≤ Real.sinh 1 * hdist u v :=
        mul_le_mul_of_nonneg_left hab (Real.sinh_nonneg_iff.mpr (by norm_num))

end

end Work.Mostow
