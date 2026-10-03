import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea7.sum_primarySet_mul
import Submission.Work.FIArea7.grossenChar_mul_primarySet

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The eigenvalue decomposition of *FI* Prop. 23.2.**  For coprime `m, n ≥ 1` every primary `e`
of norm `mn` factors uniquely as `e = w·z` with `w` primary of norm `m` and `z` primary of norm
`n` (and then `(w,z) = 1`), and the Grössencharacter is multiplicative on coprime arguments; hence

  `λ(mn) = Σ∧_{ww̄=m} ψ(w) Σ∧_{zz̄=n} ψ(z)[wz]`.

(For `w ∈ primarySet m` and `z ∈ primarySet n` with `(m,n) = 1` the coprimality `(z,w) = 1` is
automatic — a common divisor has norm dividing `gcd m n = 1` — so no coprimality indicator is
needed in the inner sum.)

Proof route: the map `(w,z) ↦ w*z` is a bijection from
`{(w,z) : w ∈ primarySet m, z ∈ primarySet n}` onto `primarySet (m*n)`.
* injective: `Commons.NumberTheory.GaussianInt.fibre_associated_of_norm_coprime` gives `w ~ w'`,
  and two associated *primary* elements are equal (each associate class of odd norm has a unique
  primary representative: `Commons.NumberTheory.GaussianInt.primary_associate_exists_unique` with
  `Commons.NumberTheory.GaussianInt.unit_eq_one_of_primary`);
* surjective: `Commons.NumberTheory.GaussianInt.factor_exists_of_norm_mul` splits `e` into a
  product of elements of norms `m`, `n`; replace each factor by its primary associate (possible
  because `e` primary forces `m` odd); the product of the two primaries is primary
  (`Work.FITop3.Witness.isPrimary_mul`), has the same norm, and is associated to `e`, hence equals
  `e` by uniqueness of the primary associate.
The weights are converted with `Work.FIArea7.grossenChar_mul_of_coprime` (already proved in
`prop232Defs`, import it) and `Work.FITop3.Witness.gnorm_mul`.
The statement is also true when `primarySet m = ∅` (e.g. `m` even, or `m` containing a prime
`≡ 3 (mod 4)` to an odd power): then `primarySet (m*n) = ∅` as well, because a primary element has
*odd* norm (`Work.FIArea7.odd_gnorm_of_isPrimary`). -/
theorem quadEigen_decomp {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (k : ℤ) (chi : GaussianInt → ℂ)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) :
    Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * n)
      = ∑ w ∈ Work.FIArea7.primarySet m, Work.FIArea7.grossenChar chi k w *
          (∑ z ∈ Work.FIArea7.primarySet n,
            Work.FIArea7.grossenChar chi k z * Work.FIArea7.JKSym (w * z)) := by
  have hsum := sum_primarySet_mul hm hn hcop
    (fun e => Work.FIArea7.grossenChar chi k e * Work.FIArea7.JKSym e)
  have hC : (Work.FIPlan.gBox (((m * n : ℕ)) : ℤ)).filter
        (fun z => Work.FIPlan.gnorm z = m * n ∧ Work.FIPlan.IsPrimary z)
      = Work.FIArea7.primarySet (m * n) := by
    rw [Work.FIArea7.primarySet]
    exact Finset.filter_congr (fun z _ => and_comm)
  rw [Work.FIArea7.quadEigen_eq_sum, hC, hsum]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [grossenChar_mul_primarySet hm hn hcop k chi hmul hw hz]
  ring

end

end Work.FIArea7
