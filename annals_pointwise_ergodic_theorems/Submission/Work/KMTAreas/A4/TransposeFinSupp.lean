/-
# The transposition identities `(transpose)` without support hypotheses on the data

`Submission/Work/Analysis/InverseTheory/Transpose.lean` proves the transposition identities

`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^*(h,g), f⟩ = ⟨Ã_N^{**}(f,h), g⟩`

under `FinSupp` hypotheses on `f, g, h`.  In fact the two `FinSupp` hypotheses on the *data*
(`f` and `g`) are never used: the finiteness of the two `tsum`s in the expansions comes from the
finite support of `h` (for the first form) and of `h` alone (for the second form, since
`Ã_N^{**}(f,h) = N⁻¹ ∑_{n} f(· + n - P(n)) h(· - P(n))` is finitely supported whenever `h` is).
This is what the duality steps of §5 need, where the data are only assumed to lie in `ℓ²(ℤ)`.

## Main results

* `Work.KMTAreas.A4.bilinPair_AhalfZ_eq_transpose_of_finSupp`;
* `Work.KMTAreas.A4.bilinPair_AhalfZ_eq_transpose₂_of_finSupp`.
-/
import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **Equation `(transpose)` of §6, first form, without hypotheses on the data:**
`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^*(h,g), f⟩`, the finiteness of both sides coming from `FinSupp h`.
(The proof is that of `bilinPair_AhalfZ_eq_transpose`, whose two hypotheses on `f` and `g` are
unused.) -/
theorem bilinPair_AhalfZ_eq_transpose_of_finSupp {f g h : ℤ → ℂ} (hh : FinSupp h)
    (N : ℕ) (P : Polynomial ℤ) :
    bilinPair (AhalfZ N P f g) h = bilinPair (AhalfTranspose N P h g) f := by
  rw [bilinPair_AhalfZ_expand hh N P, bilinPair_AhalfTranspose_expand hh N P]
  congr 1
  exact Finset.sum_congr rfl fun n _ => tsum_reindex_transpose n P

end Work.KMTAreas.A4
