import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For an integer square matrix `A`, the multiple `|det A| • y` of any integer vector `y` lies in
the `ℤ`-span of the rows of `A`. (Cramer / adjugate: `adj A * A = det A • 1` exhibits `det A • eᵢ`
in the row span.) -/
theorem natAbs_det_smul_mem_span {ρ : ℕ} (A : Matrix (Fin ρ) (Fin ρ) ℤ) (y : Fin ρ → ℤ) :
    ((A.det.natAbs : ℤ) • y) ∈ Submodule.span ℤ (Set.range (fun j => A j)) := by
  set S := Submodule.span ℤ (Set.range (fun j => A j)) with hS
  -- Every row of `A` lies in `S`.
  have hA : ∀ j, A j ∈ S := fun j => Submodule.subset_span (Set.mem_range_self j)
  -- Cramer's rule applied to `Aᵀ` writes `det A • y` as a `ℤ`-combination of the rows of `A`.
  have hd : A.det • y ∈ S := by
    have h := Matrix.mulVec_cramer A.transpose y
    rw [Matrix.det_transpose] at h
    rw [Matrix.mulVec_transpose] at h
    rw [Matrix.vecMul_eq_sum] at h
    rw [← h]
    exact Submodule.sum_mem S (fun j _ => Submodule.smul_mem S _ (hA j))
  -- Replace `det A` by `|det A|`; the two differ by a sign.
  rcases Int.natAbs_eq A.det with h | h
  · rw [h.symm]; exact hd
  · have hh : (↑(A.det.natAbs) : ℤ) = -A.det := by omega
    rw [hh, neg_smul]
    exact S.neg_mem hd

end Work.BW
