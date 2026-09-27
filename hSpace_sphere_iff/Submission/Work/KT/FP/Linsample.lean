import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.FP.Linsample` — the Laurent matrix `(1 - P) + P·T` of a matrix `P`

The image of `linSample X n P` under `Work.KT.laurentMap X` is the unit `(1 - P) + z·P` of
`Matrix (Fin n) (Fin n) C(X × S¹, ℂ)` (this is the content of `Work.KT.FP.lind_linear`), i.e. the
unit appearing in the normalisation clause of `Work.KT.FP.bott_index`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-- The Laurent matrix `(1 - P) + P·T` over the coefficient ring `C(X, ℂ)`. -/
def linSample (X : Type) [TopologicalSpace X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)) :=
  fun i j => LaurentPolynomial.C ((1 - P) i j)
    + LaurentPolynomial.C (P i j) * LaurentPolynomial.T 1

end

end Work.KT.FP
