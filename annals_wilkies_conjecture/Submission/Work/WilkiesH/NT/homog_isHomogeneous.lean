import Mathlib
import Submission.Work.WilkiesH.NT.HomogDefs

namespace Work.WilkiesH.NT

variable {K : Type*} [Field K] {n : ℕ}

/-- The total degree (sum of the exponents) of `Finsupp.cons y m` is `y` plus the total degree
of `m`. -/
lemma cons_degree (y : ℕ) (m : Fin n →₀ ℕ) :
    (Finsupp.cons y m).degree = y + m.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp

/-- The `totalDegree` of an `MvPolynomial` bounds the degree of every exponent in its support. -/
lemma degree_le_totalDegree {P : MvPolynomial (Fin n) ℤ} {m : Fin n →₀ ℕ}
    (hm : m ∈ P.support) : m.degree ≤ P.totalDegree :=
  MvPolynomial.le_totalDegree hm

theorem homog_isHomogeneous {K : Type*} [Field K] {n d : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (hdeg : P.totalDegree ≤ d) :
    (Work.WilkiesH.NT.homog (K := K) P d).IsHomogeneous d := by
  classical
  rw [homog]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  refine MvPolynomial.isHomogeneous_monomial _ ?_
  rw [cons_degree]
  have : m.degree ≤ d := le_trans (degree_le_totalDegree hm) hdeg
  omega

end Work.WilkiesH.NT
