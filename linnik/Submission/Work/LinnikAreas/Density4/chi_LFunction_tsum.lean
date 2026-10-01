import Mathlib

namespace Work.LinnikAreas.Density4

open scoped Real

/-- For `1 < re w`, the (analytically continued) Dirichlet L-function of a character `χ` modulo
`q` coincides with the naive Dirichlet series `∑' n, χ n * n ^ (-w)`.

The `n = 0` term causes no difficulty: the L-series term is `0` there, and also
`0 ^ (-w) = 0` because `w ≠ 0`. -/
theorem chi_LFunction_tsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (w : ℂ)
    (hw : 1 < w.re) :
    DirichletCharacter.LFunction χ w = ∑' n : ℕ, (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hw]
  show LSeries (fun n : ℕ => (χ (n : ZMod q) : ℂ)) w = _
  rw [LSeries]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero' (show w ≠ 0 by intro h; rw [h] at hw; norm_num at hw)]
  rw [div_eq_mul_inv, Complex.cpow_neg]

end Work.LinnikAreas.Density4
