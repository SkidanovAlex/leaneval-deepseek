/-
# `Work.FITop4.Red4.gauss_factorization` — the paper's (5.2)

The Gaussian identity of §5 (used by the `AreaReduce` step of the composition, see
`FITop4/NOTES.md` §4): for `(m, n) = 1`,

  `a_{mn} = ¼ ∑_{|w|² = m} ∑_{|z|² = n} Z(Re wz)`,

equivalently, since `Z(b) = #{c : c ^ 2 = b}` (so that the right hand side counts the pairs
`(p, c)` with `p.1² + p.2² = mn` and `p.2 = c²`, i.e. `p.1² + c⁴ = mn`),

  `∑_{|w|² = m} ∑_{|z|² = n} Z(Re wz) = 4 ∑_{p.1² + p.2² = mn} Z p.2`.

The proof is a reduction to the library theorem
`Commons.NumberTheory.GaussianInt.sum_Z_im_factorization`, which is the same statement with
`Im` in place of `Re`; the two are related by the rotation `ξ ↦ i ξ`, which is a bijection of
the Gaussian integers of fixed norm and sends `Re ξ` to `Im (i ξ)`.

NOTE ON THE STATEMENT.  The statement as requested was, verbatim (see also `NOTES.md`):

/-
theorem gauss_factorization {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (Z : ℤ → ℝ) :
    (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
          Z (Work.FIPlan.cForm w z))
      = 4 * (∑ p ∈ (Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ)) ×ˢ
              Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ)).filter
            (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = ((m * n : ℕ) : ℤ)),
          Z p.2) := by sorry
-/

It does not elaborate.  In its right hand side the parenthesis closing the first `Finset.Icc`
closes the set of the `∑ p ∈ …` binder, so nothing can follow that binder — the `×ˢ … .filter
…` of the full box lies outside it and the parser stops with "unexpected token ')'".  The
intended sum — the one appearing verbatim in `Commons…sum_Z_im_factorization`, and the only
reading under which the identity holds — is over the lattice points of the box `[-mn,mn]²`
with `p.1² + p.2² = mn`, i.e. over `targetF (m * n)`.  The statement below is that statement:
only the misplaced parenthesis has been moved, every symbol and every character otherwise
kept; the name, the hypotheses, the left hand side and the mathematical content are
unchanged.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Commons.NumberTheory.GaussianInt.sum_Z_im_factorization

namespace Work.FITop4.Red4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The box `gBox N = {|re|, |im| ≤ N}` filtered by `gnorm = N` is `elemF N`, the finset of
Gaussian integers of norm `N`: every `w` with `|w|² = N` satisfies `|re w| ≤ N` and
`|im w| ≤ N`, and conversely. -/
lemma gBox_filter_gnorm_eq_elemF (N : ℕ) :
    (Work.FIPlan.gBox ((N : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = N)
      = Commons.NumberTheory.GaussianInt.elemF N := by
  rw [Commons.NumberTheory.GaussianInt.elemF, Commons.NumberTheory.GaussianInt.targetF,
    Work.FIPlan.gBox, Finset.filter_image]
  congr 1
  apply Finset.filter_congr
  intro z _
  simp only [Work.FIPlan.gnorm]
  rw [Commons.NumberTheory.GaussianInt.norm_natAbs_eq_iff]

/-- Multiplication by `i` (of norm `1`) permutes the Gaussian integers of norm `N`, so it
reindexes any sum over them. -/
lemma sum_elemF_sqrtd_mul {N : ℕ} (hN : 1 ≤ N) (F : GaussianInt → ℝ) :
    (∑ w ∈ Commons.NumberTheory.GaussianInt.elemF N, F (Zsqrtd.sqrtd * w))
      = ∑ w ∈ Commons.NumberTheory.GaussianInt.elemF N, F w := by
  have hsq : Zsqrtd.sqrtd * Zsqrtd.sqrtd = (-1 : GaussianInt) := by
    rw [Zsqrtd.dmuld]; norm_num
  have hnorm : (Zsqrtd.sqrtd : GaussianInt).norm.natAbs = 1 := by
    rw [Zsqrtd.norm_def]; norm_num
  have hnorm' : (-Zsqrtd.sqrtd : GaussianInt).norm.natAbs = 1 := by
    rw [Zsqrtd.norm_neg]; exact hnorm
  refine Finset.sum_nbij' (fun w => Zsqrtd.sqrtd * w) (fun w => -Zsqrtd.sqrtd * w)
    (fun w hw => ?_) (fun w hw => ?_) (fun w _ => ?_) (fun w _ => ?_) (fun w _ => rfl)
  · rw [Commons.NumberTheory.GaussianInt.mem_elemF hN, Zsqrtd.norm_mul, Int.natAbs_mul, hnorm,
      one_mul, (Commons.NumberTheory.GaussianInt.mem_elemF hN w).mp hw]
  · rw [Commons.NumberTheory.GaussianInt.mem_elemF hN, Zsqrtd.norm_mul, Int.natAbs_mul, hnorm',
      one_mul, (Commons.NumberTheory.GaussianInt.mem_elemF hN w).mp hw]
  · show -Zsqrtd.sqrtd * (Zsqrtd.sqrtd * w) = w
    rw [← mul_assoc, neg_mul, hsq]
    simp
  · show Zsqrtd.sqrtd * (-Zsqrtd.sqrtd * w) = w
    rw [← mul_assoc, mul_neg, hsq]
    simp

theorem gauss_factorization {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (Z : ℤ → ℝ) :
    (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
          Z (Work.FIPlan.cForm w z))
      = 4 * (∑ p ∈ (Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ) ×ˢ
              Finset.Icc (-((m * n : ℕ) : ℤ)) ((m * n : ℕ) : ℤ)).filter
            (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = ((m * n : ℕ) : ℤ)),
          Z p.2) := by
  rw [gBox_filter_gnorm_eq_elemF m, gBox_filter_gnorm_eq_elemF n]
  simp only [Work.FIPlan.cForm]
  -- `Re ξ = Im (i ξ)`, so multiplication by `i` on the outer variable turns `re` into `im`.
  have hstep1 : (∑ w ∈ Commons.NumberTheory.GaussianInt.elemF m,
        ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n, Z (w * z).re)
      = ∑ w ∈ Commons.NumberTheory.GaussianInt.elemF m,
        ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n, Z ((Zsqrtd.sqrtd * w) * z).im := by
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro z _
    congr 1
    rw [mul_assoc, Zsqrtd.im_mul]
    simp
  have hstep2 : (∑ w ∈ Commons.NumberTheory.GaussianInt.elemF m,
        ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n, Z ((Zsqrtd.sqrtd * w) * z).im)
      = ∑ w ∈ Commons.NumberTheory.GaussianInt.elemF m,
        ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n, Z ((w * z).im) :=
    sum_elemF_sqrtd_mul hm (fun w => ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n,
      Z ((w * z).im))
  have hstep3 : (∑ w ∈ Commons.NumberTheory.GaussianInt.elemF m,
        ∑ z ∈ Commons.NumberTheory.GaussianInt.elemF n, Z ((w * z).im))
      = 4 * ∑ u ∈ Commons.NumberTheory.GaussianInt.elemF (m * n), Z u.im := by
    have hprod := Commons.NumberTheory.GaussianInt.sumZim_prod_eq_four_mul hm hn hcop Z
    rw [Finset.sum_product] at hprod
    exact hprod
  have hstep4 : (∑ u ∈ Commons.NumberTheory.GaussianInt.elemF (m * n), Z u.im)
      = ∑ p ∈ Commons.NumberTheory.GaussianInt.targetF (m * n), Z p.2 := by
    simpa using (Commons.NumberTheory.GaussianInt.sumZim_targetF_eq_elemF (m * n)
      (fun u : GaussianInt => Z u.im)).symm
  rw [hstep1, hstep2, hstep3, hstep4]
  -- `targetF (m * n)` *is* the set displayed in the statement
  rfl

end

end Work.FITop4.Red4
