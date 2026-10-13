import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Interp.V2count.card_ExpVec_succ
import Submission.Work.WilkiesH.Interp.V2count.pow_le_factorial_mul_choose

/-!
# A lower bound for the monomial count

Let `ExpVec n d` be the type of exponent vectors of total degree `≤ d` in `n`
variables, so that `monoCount n d = #(ExpVec n d)` is the number of monomials of
degree `≤ d` (see `Submission.Work.WilkiesH.Defs`).  Here we prove

  `(d + 1) ^ n ≤ n.factorial * monoCount n d`,

i.e. that `n!` times the number of monomials of degree `≤ d` in `n` variables
dominates `(d+1)^n`.

The mathematical content is the classical count of exponent vectors,

  `monoCount n d = (n + 1).multichoose d = (n + d).choose n`,

from which the statement follows because

  `n.factorial * (n + d).choose n = (d + 1).ascFactorial n = ∏_{k=1}^{n} (d + k)`,

a product of `n` factors each `≥ d + 1`.

The count is obtained by induction on the number of variables from the recursion

  `monoCount (n+1) d = ∑_{j ≤ d} monoCount n j`,

(splitting off the last exponent into `k = a_n ≤ d` and a remainder of degree
`≤ d - k`), together with the stars-and-bars identity `Nat.sum_range_multichoose`
for `∑_{j ≤ d} (n+1).multichoose j`.  The two analytic inputs are proved in the
sibling files of this directory:

* `Submission.Work.WilkiesH.Interp.V2count.card_ExpVec_succ` :
  `#(ExpVec (n+1) d) = ∑_{j ≤ d} #(ExpVec n j)`;
* `Submission.Work.WilkiesH.Interp.V2count.pow_le_factorial_mul_choose` :
  `(d + 1)^n ≤ n! · (n + d).choose n`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Interp.V2count

open Work.WilkiesH

/-- **Lower bound for the monomial count.**  The number of monomials of total
degree `≤ d` in `n` variables, multiplied by `n!`, is at least `(d + 1)^n`. -/
theorem monoCount_factorial_lower (n d : ℕ) :
    (d + 1) ^ n ≤ n.factorial * Work.WilkiesH.monoCount n d := by
  -- Step 1: `monoCount n d` is the number of weak compositions, `(n+1).multichoose d`.
  have hmc : Work.WilkiesH.monoCount n d = (n + 1).multichoose d := by
    induction n generalizing d with
    | zero => simp [Work.WilkiesH.monoCount, Work.WilkiesH.ExpVec, Nat.multichoose_one]
    | succ n ih =>
      rw [Work.WilkiesH.monoCount, card_ExpVec_succ n d]
      rw [Finset.sum_congr rfl (fun j _ => by rw [← Work.WilkiesH.monoCount, ih j])]
      rw [Nat.sum_range_multichoose d (n + 1), Nat.multichoose_eq]
      have htop : (n + 2) + d - 1 = d + (n + 1) := by omega
      rw [htop]
      exact Nat.choose_symm_of_eq_add (by omega)
  -- Step 2: the ascending factorial `(d+1)(d+2)⋯(d+n)` dominates `(d+1)^n`.
  rw [hmc, Nat.multichoose_eq]
  have htop : (n + 1) + d - 1 = n + d := by omega
  rw [htop]
  refine le_trans (pow_le_factorial_mul_choose n d) (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simpa [Nat.add_sub_cancel] using (Nat.choose_symm (show d ≤ n + d by omega))

end Work.WilkiesH.Interp.V2count
