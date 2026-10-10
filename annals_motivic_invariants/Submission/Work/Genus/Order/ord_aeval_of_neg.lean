import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.Order.ord_sum_gt
import Submission.Work.Genus.Order.aeval_eq_sum_support

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial

/-- **The term of strictly minimal order dominates a finite sum.**  If `j ∈ S` is the (unique)
index at which the summand `t j` has strictly smaller order than every other summand, and that
order is negative, then the order of the whole sum is the order of `t j`.

The proof splits the sum into the dominant term `t j` and the rest, applies the strict
non-archimedean equality `ord_add_eq_of_lt` (valid because `ord π (t j) < 0` forces `t j ≠ 0`), and
bounds the order of the rest below by `ord π (t j)` with `ord_sum_gt`. -/
theorem ord_sum_eq_of_unique_min {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {S : Finset ℕ} {t : ℕ → RatFunc F} {j : ℕ} (hj : j ∈ S)
    (hneg : Work.Genus.ord π (t j) < 0)
    (hlt : ∀ i ∈ S, i ≠ j → Work.Genus.ord π (t j) < Work.Genus.ord π (t i)) :
    Work.Genus.ord π (∑ i ∈ S, t i) = Work.Genus.ord π (t j) := by
  classical
  have htj : t j ≠ 0 := by
    intro h0
    rw [h0, ord_zero] at hneg
    exact absurd hneg (lt_irrefl 0)
  have hsplit : (∑ i ∈ S, t i) = t j + ∑ i ∈ S.erase j, t i := by
    conv_lhs => rw [← Finset.insert_erase hj]
    rw [Finset.sum_insert (Finset.notMem_erase j S)]
  rw [hsplit]
  exact ord_add_eq_of_lt hπ htj
    (ord_sum_gt hπ hneg fun i hi ↦
      hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))

/-- **Leading term dominates at a pole.**  If `x` has a pole at the place of the irreducible `π`
of order `-m` (`m > 0`) then `A(x)` has a pole of order `A.natDegree * m` there: the term of
highest degree in `A` dominates strictly, every other term having strictly larger order.  In
particular `A(x) ≠ 0`.

Route: expand `A` as `∑ i in Finset.range (A.natDegree + 1), C (A.coeff i) * X ^ i` (or use
`Polynomial.as_sum_range_C_mul_X_pow`), compute `ord π (C (A.coeff i) * x ^ i) = i * ord π x` for
`i > 0` with `ord π x < 0` and `A.coeff i ≠ 0` (`ord_C_mul`, `ord_pow`), note these are all
distinct with unique strict minimum at `i = A.natDegree` (whose coefficient is non-zero), and
conclude by successive `ord_add_eq_of_lt`.  Terms with `A.coeff i = 0` should be dropped from the
sum (e.g. sum over the support `A.support`). -/
theorem ord_aeval_of_neg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {A : Polynomial F} (hA : 0 < A.natDegree) {x : RatFunc F} (hx : x ≠ 0)
    (h : Work.Genus.ord π x < 0) :
    Work.Genus.ord π (Polynomial.aeval x A) = A.natDegree * Work.Genus.ord π x := by
  classical
  have hAne : A ≠ 0 := by
    intro h0
    rw [h0] at hA
    exact absurd hA (by simp)
  have hcoeff : A.coeff A.natDegree ≠ 0 := by
    simpa using (Polynomial.leadingCoeff_ne_zero.mpr hAne)
  have hmem : A.natDegree ∈ A.support := Polynomial.mem_support_iff.mpr hcoeff
  -- The order of each summand of the expansion, indexed by the support of `A`.
  have hterm : ∀ i ∈ A.support,
      Work.Genus.ord π (algebraMap F (RatFunc F) (A.coeff i) * x ^ i)
        = i * Work.Genus.ord π x := by
    intro i hi
    have hc : A.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    rw [ord_C_mul hc (x ^ i), ord_pow hπ hx i]
  -- The leading term has a strictly negative order (there is a genuine pole).
  have hneg : Work.Genus.ord π (algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree)
      < 0 := by
    rw [hterm A.natDegree hmem]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hA) h
  -- Every other term has strictly larger order: `i < A.natDegree` and `ord π x < 0`.
  have hlt : ∀ i ∈ A.support, i ≠ A.natDegree →
      Work.Genus.ord π (algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree)
        < Work.Genus.ord π (algebraMap F (RatFunc F) (A.coeff i) * x ^ i) := by
    intro i hi hiA
    rw [hterm A.natDegree hmem, hterm i hi]
    have hi' : i < A.natDegree :=
      lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hi) hiA
    exact mul_lt_mul_of_neg_right (by exact_mod_cast hi') h
  have hkey := ord_sum_eq_of_unique_min (π := π) (S := A.support)
    (t := fun i ↦ algebraMap F (RatFunc F) (A.coeff i) * x ^ i) hπ hmem hneg hlt
  calc Work.Genus.ord π (Polynomial.aeval x A)
      = Work.Genus.ord π (∑ i ∈ A.support, algebraMap F (RatFunc F) (A.coeff i) * x ^ i) := by
        rw [aeval_eq_sum_support]
    _ = Work.Genus.ord π (algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree) :=
        hkey
    _ = A.natDegree * Work.Genus.ord π x := hterm A.natDegree hmem

end Work.Genus.Order
