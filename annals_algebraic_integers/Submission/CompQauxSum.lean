import Submission.CompQNums
import Submission.Bclps

/-!
# Degree bound of the ε-sum

Helper for `Submission/CompQRoots.lean`: with `d = (D−1)·r`, for
`1 ≤ t ≤ d` the auxiliary polynomial `auxPoly t` has degree `t`, hence each
term of the ε-sum and the whole sum have degree `≤ d`.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQauxSum

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- the auxiliary-degree `d = (D−1)·r` (same as in `CompQRoots`). -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r

/-- each ε-term has degree `≤ d`. -/
theorem term_natDegree_le (r : ℕ) (eps : ℕ → ℝ) :
    ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) →
      (Polynomial.C (eps t) * Bclps.auxPoly t).natDegree ≤ d r := by
  intro t ht
  calc
    (C (eps t) * Bclps.auxPoly t).natDegree ≤ (Bclps.auxPoly t).natDegree := by
      exact Polynomial.natDegree_C_mul_le (eps t) (Bclps.auxPoly t)
    _ = t := Bclps.auxPoly_natDegree t
    _ ≤ d r := (Finset.mem_Icc.mp ht).2

/-- the whole ε-sum has degree `≤ d`. -/
theorem aux_sum_natDegree_le (r : ℕ) (eps : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t).natDegree ≤ d r := by
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.Icc 1 (d r))
    (fun t => Polynomial.C (eps t) * Bclps.auxPoly t) ?_
  intro t ht
  exact term_natDegree_le r eps t ht

end Submission.CompQauxSum
