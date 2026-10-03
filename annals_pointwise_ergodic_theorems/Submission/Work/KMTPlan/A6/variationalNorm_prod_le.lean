/-
# The variational norm is multiplicative: `‖a·b‖_{V^r} ≤ 2‖a‖_{V^r}‖b‖_{V^r}`

For `r ≥ 1` the `r`-variational norm of a pointwise product of two sequences is bounded by the
product of the variational norms (up to the absolute constant `2`).  Writing
`‖a‖_{V^r} = sup_n ‖a n‖ + V^r(a)` (`Work.Analysis...`/`Submission.VarNorm`), the two parts are
controlled separately:

* the sup part: `sup_n ‖a n * b n‖ ≤ (sup_n ‖a n‖)(sup_n ‖b n‖)` (`iSup_enorm_mul_le`);
* the variation part: splitting the difference of the products as
  `Δ(ab)_i = (Δa)_i · b(N(i+1)) + a(N i) · (Δb)_i` and bounding the `ℓ^r` norm of a componentwise
  product by the sup of the multipliers times the `ℓ^r` norm of the other factor
  (`Work.KMTPlan.A6.toLp_mul_norm_le`), one gets
  `V^r(ab) ≤ (sup‖b‖)·V^r(a) + (sup‖a‖)·V^r(b)` (`varPart_mul_le`);
* the arithmetic `A*B + (B*Va + A*Vb) ≤ 2*((A+Va)*(B+Vb))` (`Work.KMTPlan.A6.mul_prod_add_le`)
  turns the sum of the two estimates into the product of the variational norms.

This is the elementary product inequality needed to bound variational norms of bilinear
expressions by the variational norms of their factors.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowDefs
import Submission.Work.KMTPlan.A6.toLp_mul_norm_le
import Submission.Work.KMTPlan.A6.mul_prod_add_le

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.style.haveILetI false

/-- **The variation part of a pointwise product.**  For `r ≥ 1`,
`V^r(a·b) ≤ (sup_n ‖b n‖)·V^r(a) + (sup_n ‖a n‖)·V^r(b)`.

The difference of the products along a monotone selection `N` is split as
`a(N(i+1))b(N(i+1)) - a(N i)b(N i) = (Δa)_i·b(N(i+1)) + a(N i)·(Δb)_i`; the `ℓ^r` norm of each
piece is bounded by the sup of its multiplier times the `ℓ^r` norm of the difference vector
(`toLp_mul_norm_le`). -/
lemma varPart_mul_le {r : NNReal} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n => a n * b n)
      ≤ (⨆ n, ‖b n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r a
        + (⨆ n, ‖a n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r b := by
  haveI : Fact (1 ≤ (r : ENNReal)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  show ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
      (fun i : Fin J => a (N (i + 1)) * b (N (i + 1)) - a (N i) * b (N i))‖ ≤ _
  have hsplit : WithLp.toLp (r : ENNReal)
        (fun i : Fin J => a (N (i + 1)) * b (N (i + 1)) - a (N i) * b (N i))
      = WithLp.toLp (r : ENNReal) (fun i : Fin J => (a (N (i + 1)) - a (N i)) * b (N (i + 1)))
        + WithLp.toLp (r : ENNReal) (fun i : Fin J => a (N i) * (b (N (i + 1)) - b (N i))) := by
    rw [← WithLp.toLp_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    ring
  have hsupb : (⨆ i : Fin J, ‖b (N (i + 1))‖ₑ) ≤ ⨆ n, ‖b n‖ₑ :=
    iSup_le (fun i => le_iSup (fun n => ‖b n‖ₑ) (N (i + 1)))
  have hsupa : (⨆ i : Fin J, ‖a (N i)‖ₑ) ≤ ⨆ n, ‖a n‖ₑ :=
    iSup_le (fun i => le_iSup (fun n => ‖a n‖ₑ) (N i))
  have hva : ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
      (fun i : Fin J => a (N (i + 1)) - a (N i))‖
      ≤ Submission.PointwiseErgodicTheorems.varPart r a :=
    le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  have hvb : ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
      (fun i : Fin J => b (N (i + 1)) - b (N i))‖
      ≤ Submission.PointwiseErgodicTheorems.varPart r b :=
    le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  rw [hsplit]
  calc ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
          (fun i : Fin J => (a (N (i + 1)) - a (N i)) * b (N (i + 1)))
        + WithLp.toLp (r : ENNReal) (fun i : Fin J => a (N i) * (b (N (i + 1)) - b (N i)))‖
      ≤ ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
            (fun i : Fin J => (a (N (i + 1)) - a (N i)) * b (N (i + 1)))‖
          + ENNReal.ofReal ‖WithLp.toLp (r : ENNReal)
            (fun i : Fin J => a (N i) * (b (N (i + 1)) - b (N i)))‖ := by
        rw [ofReal_norm, ofReal_norm, ofReal_norm]
        exact enorm_add_le _ _
    _ ≤ (⨆ i : Fin J, ‖b (N (i + 1))‖ₑ)
          * ENNReal.ofReal ‖WithLp.toLp (r : ENNReal) (fun i : Fin J => a (N (i + 1)) - a (N i))‖
        + (⨆ i : Fin J, ‖a (N i)‖ₑ)
          * ENNReal.ofReal ‖WithLp.toLp (r : ENNReal) (fun i : Fin J => b (N (i + 1)) - b (N i))‖ := by
        refine add_le_add ?_ ?_
        · simp only [← ofReal_norm]
          exact toLp_mul_norm_le hr _ _
        · simp only [← ofReal_norm]
          have h2 : (fun i : Fin J => a (N i) * (b (N (i + 1)) - b (N i)))
              = (fun i : Fin J => (b (N (i + 1)) - b (N i)) * a (N i)) := by
            funext i; rw [mul_comm]
          rw [h2]
          exact toLp_mul_norm_le hr _ _
    _ ≤ (⨆ n, ‖b n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r a
        + (⨆ n, ‖a n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r b := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_left hsupb _).trans (mul_le_mul_right hva _)
        · exact (mul_le_mul_left hsupa _).trans (mul_le_mul_right hvb _)

/-- **The sup part of a pointwise product.**  `sup_n ‖a n · b n‖ ≤ (sup_n ‖a n‖)(sup_n ‖b n‖)`. -/
lemma iSup_enorm_mul_le (a b : ℕ → ℂ) :
    (⨆ n, ‖a n * b n‖ₑ) ≤ (⨆ n, ‖a n‖ₑ) * (⨆ n, ‖b n‖ₑ) := by
  refine iSup_le (fun n => ?_)
  show ‖a n * b n‖ₑ ≤ _
  calc ‖a n * b n‖ₑ = ‖a n‖ₑ * ‖b n‖ₑ := enorm_mul _ _
    _ ≤ (⨆ n, ‖a n‖ₑ) * (⨆ n, ‖b n‖ₑ) :=
        (mul_le_mul_left (le_iSup (fun n => ‖a n‖ₑ) n) _).trans
          (mul_le_mul_right (le_iSup (fun n => ‖b n‖ₑ) n) _)

open MeasureTheory Polynomial Finset Filter Topology in
open scoped ENNReal NNReal BigOperators in
theorem variationalNorm_prod_le {r : NNReal} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => a n * b n)
      ≤ 2 * (PointwiseErgodicTheorems.variationalNorm r a
          * PointwiseErgodicTheorems.variationalNorm r b) := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  calc (⨆ n, ‖(fun n => a n * b n) n‖ₑ)
        + Submission.PointwiseErgodicTheorems.varPart r (fun n => a n * b n)
      ≤ (⨆ n, ‖a n‖ₑ) * (⨆ n, ‖b n‖ₑ)
        + ((⨆ n, ‖b n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r a
          + (⨆ n, ‖a n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r b) :=
        add_le_add (iSup_enorm_mul_le a b) (varPart_mul_le hr a b)
    _ ≤ 2 * (((⨆ n, ‖a n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r a)
          * ((⨆ n, ‖b n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r b)) :=
        mul_prod_add_le
    _ = 2 * (PointwiseErgodicTheorems.variationalNorm r a
          * PointwiseErgodicTheorems.variationalNorm r b) := by
        rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
          Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]

end Work.KMTPlan.A6
