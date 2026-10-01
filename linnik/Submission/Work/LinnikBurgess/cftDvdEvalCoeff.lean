import Mathlib

namespace Work.LinnikBurgess

/-- If every coefficient of an integer polynomial `G` is divisible by `p`, then
`G` evaluated at any integer is divisible by `p`. -/
lemma cftDvdEvalCoeff {p : ℕ} (G : Polynomial ℤ) (h : ∀ i, (p : ℤ) ∣ G.coeff i) (x : ℤ) :
    (p : ℤ) ∣ G.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (h i) _

end Work.LinnikBurgess
