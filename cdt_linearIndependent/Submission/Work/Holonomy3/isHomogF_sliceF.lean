import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

namespace Work.Holonomy3

set_option linter.unusedVariables false in
/-- Slicing preserves homogeneity: the family of coefficients of the `t`-th power of the first
variable, for `t = n 0`, is homogeneous of degree `D - n 0` whenever `c` is homogeneous of
degree `D` and `n` is a multi-index in the support of `c`.

Indeed, if `m` lies in the support of the slice, then `c (consIdx (n 0) m) ≠ 0`, so
`consIdx (n 0) m` lies in the support of `c` and has degree `D`.  Since the degree of a
prepended index is `n 0 + m.degree`, this forces `m.degree = D - n 0`. -/
theorem isHomogF_sliceF {d : ℕ} (c : (Fin (d+1) →₀ ℕ) →₀ ℂ) {D : ℕ} (hhom : IsHomogF c D)
    {n : Fin (d+1) →₀ ℕ} (hn : n ∈ c.support) :
    IsHomogF (sliceF c (n 0)) (D - n 0) := by
  intro m hm
  -- `m` is in the support of the slice, so `c (consIdx (n 0) m) ≠ 0`.
  have hm0 : sliceF c (n 0) m ≠ 0 := Finsupp.mem_support_iff.mp hm
  rw [sliceF_apply] at hm0
  -- hence `consIdx (n 0) m` is in the support of `c`, and has degree `D`.
  have hmem : consIdx (n 0) m ∈ c.support := Finsupp.mem_support_iff.mpr hm0
  have hdeg : (consIdx (n 0) m).degree = D := hhom _ hmem
  -- the degree of a prepended index is `n 0 + m.degree`.
  rw [consIdx_degree] at hdeg
  omega

end Work.Holonomy3
