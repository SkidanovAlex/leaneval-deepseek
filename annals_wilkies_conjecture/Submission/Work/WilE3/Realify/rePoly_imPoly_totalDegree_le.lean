import Mathlib
import Submission.Work.WilE3.Realify.Defs

namespace Work.WilE3.Realify

/-- A coefficientwise "coordinate projection" of a polynomial (sum over the support of the
monomials re-scaled by a function of the exponents) has total degree at most that of `p` when the
new coefficients are built from `p`'s.  Concretely, for `g : ℂ → ℝ` we have
`(∑ m ∈ p.support, monomial m (g (p.coeff m))).totalDegree ≤ p.totalDegree`. -/
theorem coeffProj_totalDegree_le {k r : ℕ} (g : ℂ → ℝ)
    (p : MvPolynomial (Sig k r) ℂ) :
    (∑ m ∈ p.support, MvPolynomial.monomial m (g (p.coeff m))).totalDegree ≤ p.totalDegree := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_le_iff]
  intro m hm
  exact le_trans (MvPolynomial.totalDegree_monomial_le m _) (MvPolynomial.le_totalDegree hm)

theorem rePoly_imPoly_totalDegree_le {k r : ℕ} (p : MvPolynomial (Sig k r) ℂ) :
    (rePoly p).totalDegree ≤ p.totalDegree ∧ (imPoly p).totalDegree ≤ p.totalDegree := by
  constructor
  · unfold rePoly
    exact coeffProj_totalDegree_le Complex.re p
  · unfold imPoly
    exact coeffProj_totalDegree_le Complex.im p

end Work.WilE3.Realify
