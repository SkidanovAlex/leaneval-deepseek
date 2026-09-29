import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_helpers
import Submission.Work.Haupt.sf_summable_nat
import Submission.Work.Haupt.neg_part_tsum

/-!
# The semi-finite split `∑_{n ∈ ℤ} sfTerm = Afun + Bfun`

`sfTerm` is the summand of the semi-finite sum for the Jacobi triple product,
`semi_finite_split` decomposes the ℤ-indexed sum into its `n ≥ 0` part (`Afun`) and
the finitely many terms with `-m ≤ n ≤ -1`, which are rewritten, using the
reciprocity `qpInt (q^(m+1)) q (-k) = ((q^(m+1-k);q)_k)⁻¹`, into the finite sum `Bfun`.
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

theorem semifinite_split {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) (m : ℕ) :
    (∑' n : ℤ, sfTerm q z m n) = Afun q z m + Bfun q z m := by
  have _ : z ≠ 0 := hz
  -- summability of the two halves
  have hsumNat : Summable fun n : ℕ => sfTerm q z m (n : ℤ) :=
    (sf_summable_nat (q := q) (z := z) hq m).congr (fun n => (sfTerm_natCast q z m n).symm)
  have hsumNeg : Summable fun n : ℕ => sfTerm q z m (-((n : ℤ) + 1)) := by
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Finset.finite_toSet (Finset.range m)) ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hm
    exact hn (sfTerm_neg_eq_zero hq (by omega : m + 1 ≤ n + 1))
  -- split the ℤ-sum into the two ℕ-sums
  rw [tsum_of_nat_of_neg_add_one hsumNat hsumNeg]
  -- the `n ≥ 0` part is `Afun`, the negative part is the finitely supported sum `Bfun`
  have h1 : (∑' n : ℕ, sfTerm q z m (n : ℤ)) = Afun q z m :=
    tsum_congr (fun n => sfTerm_natCast q z m n)
  have h2 : (∑' n : ℕ, sfTerm q z m (-((n : ℤ) + 1))) = Bfun q z m :=
    neg_part_tsum hq m
  rw [h1, h2]

end Work.Haupt
