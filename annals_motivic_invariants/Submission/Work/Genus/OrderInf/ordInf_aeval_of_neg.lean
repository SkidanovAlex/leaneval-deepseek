import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.aeval_eq_sum_support
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

open Polynomial

/-- `ordInf 0 = 0`: the zero function has neither a zero nor a pole at infinity. -/
private lemma ordInf_zero {F : Type*} [Field F] : Work.Genus.ordInf (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ordInf, RatFunc.intDegree_zero]

/-- **A finite sum whose terms all have order at infinity bigger than `c < 0` again has order
bigger than `c`.**  This is the weak non-archimedean inequality
(`min_ordInf_le_ordInf_add`) iterated over the summands. -/
private lemma lt_ordInf_sum {F : Type*} [Field F] {ι : Type*} {S : Finset ι}
    {t : ι → RatFunc F} {c : ℤ} (hc : c < 0) (h : ∀ i ∈ S, c < Work.Genus.ordInf (t i)) :
    c < Work.Genus.ordInf (∑ i ∈ S, t i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [ordInf_zero] using hc
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have ha' : c < Work.Genus.ordInf (t a) := h a (Finset.mem_insert_self a S)
    have ih' : c < Work.Genus.ordInf (∑ i ∈ S, t i) :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    rcases eq_or_ne (t a) 0 with h0 | hna
    · rw [h0, zero_add]; exact ih'
    rcases eq_or_ne (∑ i ∈ S, t i) 0 with h0 | hns
    · rw [h0, add_zero]; exact ha'
    rcases eq_or_ne (t a + ∑ i ∈ S, t i) 0 with h0 | hsum
    · rw [h0, ordInf_zero]; exact hc
    · exact lt_of_lt_of_le (lt_min ha' ih')
        (min_ordInf_le_ordInf_add hna hns hsum)

/-- **Leading term dominates at infinity.**  If `x` has a pole of order `-m` at infinity
(`ordInf x < 0`) then `A(x)` has order `A.natDegree * m` there: the term of highest degree is the
unique strict minimum, all others having strictly larger order.  Route: as in the finite-place
`Work.Genus.Order.ord_aeval_of_neg`, expand along `A.support` and use `ordInf_C_mul`, `ordInf_pow`
and `ordInf_add_eq_of_lt`. -/
theorem ordInf_aeval_of_neg {F : Type*} [Field F] {A : Polynomial F} (hA : 0 < A.natDegree)
    {x : RatFunc F} (hx : x ≠ 0) (h : Work.Genus.ordInf x < 0) :
    Work.Genus.ordInf (Polynomial.aeval x A) = A.natDegree * Work.Genus.ordInf x := by
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
      Work.Genus.ordInf (algebraMap F (RatFunc F) (A.coeff i) * x ^ i)
        = i * Work.Genus.ordInf x := by
    intro i hi
    have hc : A.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    rw [ordInf_C_mul hc (x ^ i), ordInf_pow hx i]
  -- The leading term has a strictly negative order (there is a genuine pole).
  have hneg : Work.Genus.ordInf (algebraMap F (RatFunc F) (A.coeff A.natDegree)
      * x ^ A.natDegree) < 0 := by
    rw [hterm A.natDegree hmem]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hA) h
  -- Every other term has strictly larger order: `i < A.natDegree` and `ordInf x < 0`.
  have hlt : ∀ i ∈ A.support, i ≠ A.natDegree →
      Work.Genus.ordInf (algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree)
        < Work.Genus.ordInf (algebraMap F (RatFunc F) (A.coeff i) * x ^ i) := by
    intro i hi hiA
    rw [hterm A.natDegree hmem, hterm i hi]
    have hi' : i < A.natDegree :=
      lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hi) hiA
    exact mul_lt_mul_of_neg_right (by exact_mod_cast hi') h
  have htj : algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree ≠ 0 := by
    intro h0
    rw [h0, ordInf_zero] at hneg
    exact absurd hneg (lt_irrefl 0)
  -- The whole tail has order strictly larger than the leading term.
  have htail : Work.Genus.ordInf (algebraMap F (RatFunc F) (A.coeff A.natDegree)
        * x ^ A.natDegree)
      < Work.Genus.ordInf (∑ i ∈ A.support.erase A.natDegree,
          algebraMap F (RatFunc F) (A.coeff i) * x ^ i) :=
    lt_ordInf_sum hneg fun i hi =>
      hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  rw [Work.Genus.Order.aeval_eq_sum_support]
  rw [show (∑ i ∈ A.support, algebraMap F (RatFunc F) (A.coeff i) * x ^ i)
      = algebraMap F (RatFunc F) (A.coeff A.natDegree) * x ^ A.natDegree
        + ∑ i ∈ A.support.erase A.natDegree,
            algebraMap F (RatFunc F) (A.coeff i) * x ^ i from by
    conv_lhs => rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase A.natDegree A.support)]]
  rw [ordInf_add_eq_of_lt htj htail, hterm A.natDegree hmem]

end Work.Genus.OrderInf
