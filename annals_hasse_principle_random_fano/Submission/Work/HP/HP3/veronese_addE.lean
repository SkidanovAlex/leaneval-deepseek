import Mathlib
import Submission.Work.HP.HP3.VeroProdExtra

namespace Work.HP.HP3

/-- `ν_{d,n}(x)(m + e_j) = ν_{d-1,n}(x)(m) · x_j`: shifting the exponent vector of a monomial by
`e_j` multiplies the corresponding monomial of the Veronese map by `x_j`. -/
theorem veronese_addE (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) (x : Fin (n + 1) → ℤ) :
    veronese d n x (addE d n hd m j) = veronese (d - 1) n x m * x j := by
  simp only [veronese, addE_val]
  rw [Finset.prod_congr rfl (fun i _ => by rw [pow_add]), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Work.HP.HP3
