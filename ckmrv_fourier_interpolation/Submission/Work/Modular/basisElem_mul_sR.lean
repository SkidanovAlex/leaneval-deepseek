import Mathlib
import Submission.Work.Modular.GroupAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- Right multiplication by `S` on the six basis elements is given by the matrix `sigmaS`: this is
the computation `M i * S = ∑ j, σ(S) i j • M j` of the paper (it uses only `S ^ 2 = 1`). -/
theorem basisElem_mul_sR (i : Fin 6) :
    basisElem i * sR = ∑ j, sigmaS i j • basisElem j := by
  fin_cases i
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
    rw [mul_assoc, ← pow_two, sR_sq, mul_one]
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
    rw [← pow_two, sR_sq]
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
  · simp [basisElem, sigmaS, Fin.sum_univ_six]
    rw [mul_assoc, ← pow_two, sR_sq, mul_one]

end Work.Modular
