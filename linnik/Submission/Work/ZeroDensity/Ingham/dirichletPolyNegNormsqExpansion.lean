import Mathlib
import Submission.Work.Analysis.Complex.cpow_nat_eq_exp
import Submission.Work.Analysis.Complex.dirichletPoly_normsq_expansion

namespace Work.ZeroDensity.Ingham

/-- Expansion of the squared norm of the Dirichlet-polynomial `∑ b n * n ^ (-(t * I))` as a
double sum. This is the `t ↦ -t` specialization of
`Work.Analysis.Complex.dirichletPoly_normsq_expansion`, where the exponent `-(t * I)` at the
`m`-th term and the conjugate exponent `t * I` at the `n`-th term combine into the phase
`exp (I * (t * (log n - log m)))`. -/
lemma dirichletPolyNegNormsqExpansion (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (b m * (starRingEnd ℂ) (b n)) *
            Complex.exp (Complex.I * (((t : ℝ) * (Real.log (n : ℝ) - Real.log (m : ℝ)) : ℝ) : ℂ))).re := by
  have h := Work.Analysis.Complex.dirichletPoly_normsq_expansion b N (-t)
  rw [Complex.ofReal_neg, neg_mul] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl; intro m hm
  apply Finset.sum_congr rfl; intro n hn
  rw [show ((-t) * (Real.log (m : ℝ) - Real.log (n : ℝ)))
        = t * (Real.log (n : ℝ) - Real.log (m : ℝ)) by ring]

end Work.ZeroDensity.Ingham
