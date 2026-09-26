import Mathlib
import Submission.Work.Modular.GroupAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- The first rows of the six matrices `σ (M i)` are the standard basis vectors: this is the
paper's check that makes `1, T, TS, S, ST, STS` linearly independent modulo `I`. -/
theorem sigmaAlg_basisElem_row (i : Fin 6) : (sigmaAlg (basisElem i)) 0 = Pi.single i 1 := by
  -- `basisElem` is `![1, T, TS, S, ST, STS]`, `sigmaAlg` is multiplicative and sends the
  -- generators `sR`, `tR` to `sigmaS`, `sigmaT`; the row `0` of each of the six resulting
  -- matrices is one of the standard basis vectors (by direct computation on `Fin 6`).
  fin_cases i <;>
    ext j <;> fin_cases j <;>
    simp [basisElem, map_mul, sigmaAlg_sR, sigmaAlg_tR, sigmaS, sigmaT,
      Matrix.mul_apply, Fin.sum_univ_six, Pi.single, Function.update]

end Work.Modular
