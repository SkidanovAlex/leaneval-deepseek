import Mathlib

namespace Work.WilE2

/-- The determinant is a finite sum over permutations of products of the entries, hence it is
`C^1` (indeed smooth) as a function of the matrix entries. -/
theorem contDiff_det {n : ℕ} :
    ContDiff ℝ 1 (fun M : Fin n → Fin n → ℝ => Matrix.det M) := by
  have h : ContDiff ℝ 1 (fun M : Fin n → Fin n → ℝ =>
      ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, M (σ i) i) := by
    refine ContDiff.sum (fun σ _ => ?_)
    refine ContDiff.mul contDiff_const ?_
    refine contDiff_prod (fun i _ => ?_)
    fun_prop
  convert h using 2 with M
  exact Matrix.det_apply' M

end Work.WilE2
