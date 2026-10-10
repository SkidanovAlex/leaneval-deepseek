import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.JunkLinAux

/-- If `f : K[X₀,…,Xₙ]` has total degree `≤ 1`, then after splitting off the variable `X₀` (via
`MvPolynomial.finSuccEquiv K n`, which sends `X 0` to `Polynomial.X` and `X (i+1)` to
`Polynomial.C (X i)`), the resulting polynomial has `natDegree ≤ 1`.

Route: `Polynomial.natDegree_le_iff_coeff_eq_zero` reduces the goal to
`(MvPolynomial.finSuccEquiv K n f).coeff N = 0` for `N > 1`.  If that coefficient were nonzero,
`MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f N h` gives
`((finSuccEquiv K n f).coeff N).totalDegree + N ≤ f.totalDegree ≤ 1`, hence `N ≤ 1`, a contradiction
(`omega` closes it).  (Alternatively: `MvPolynomial.natDegree_finSuccEquiv` identifies the
`natDegree` with `f.degreeOf 0`, which is `≤ f.totalDegree`.) -/
lemma finSuccEquiv_natDegree_le_one {K : Type} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.totalDegree ≤ 1) :
    (MvPolynomial.finSuccEquiv K n f).natDegree ≤ 1 := by
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact le_trans (MvPolynomial.degreeOf_le_totalDegree f 0) hf

end Work.MotK.JunkLinAux
