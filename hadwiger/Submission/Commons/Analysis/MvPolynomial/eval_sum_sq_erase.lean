import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.MvPolynomial

open scoped BigOperators

theorem eval_sum_sq_erase {n : ℕ} [NeZero n] (y : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval (fun i : Fin n => y i)
      (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n),
        (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ 2)
    = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), (y i) ^ 2 := by
  simp

end Commons.Analysis.MvPolynomial