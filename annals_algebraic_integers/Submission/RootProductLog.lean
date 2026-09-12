import Submission.LogProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Root-product logarithm (C3)

For nonzero `Q ∈ ℤ[x]` with nonzero constant term (so no root is zero), the
sum over the complex roots (with multiplicity) of `log‖z‖` satisfies

    Σ_{z ∈ rootMultiset Q} log‖z‖ = log‖Q(0)‖ − log‖lc(Q)‖.

## Route
1. From the factorization over ℂ (`Qc = C(lc)·∏_{z}(X − C z)`,
   `rootMultiset Q = Qc.aroots ℂ` — see `Submission.LogProductMeasure`),
   compare constant terms: `Qc` evaluated at 0 is
   `lc·∏_{z} (0 − z) = lc·(−1)^n·∏_z z`, so
       ∏_{z ∈ rootMultiset Q} z = (−1)^n · Q(0)/lc .
2. Norms: `‖∏_z z‖ = ∏_z ‖z‖`, and `‖(−1)^n·Q(0)/lc‖ = ‖Q(0)‖/‖lc‖`
   (norms of integer casts are ≥ 0; `‖lc‖ ≠ 0`).
3. Logarithms: `log(∏_z ‖z‖) = Σ_z log‖z‖` and
   `log(‖Q(0)‖/‖lc‖) = log‖Q(0)‖ − log‖lc‖`, giving the statement.

The roots multiset is `Submission.LogProductMeasure.rootMultiset Q` (sum over
a `Multiset` via `.sum` of the mapped function).  `Q.coeff 0` is the constant
term; `Q.leadingCoeff` the leading coefficient.  Vieta: derive from the
factorization identity you already proved in `LogProductMeasure` (or state it
there as a helper and reuse); `log_mul`, `log_div`, `norm_mul`, `norm_div`.
-/

noncomputable section

open MeasureTheory
open scoped Real
open Polynomial

namespace Submission.RootProductLog

open Submission.LogProductMeasure

/-- Factorization evaluated at zero:
`Q(0) = lc · ∏_{z ∈ roots} (0 − z)` over ℂ. -/
lemma eval_zero_factor (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    (((Q.coeff 0 : ℤ) : ℂ)) =
      (((Q.leadingCoeff : ℤ) : ℂ)) *
        ((rootMultiset Q).map (fun z : ℂ => (0 : ℂ) - z)).prod := by
  have hfac : Q.map (algebraMap ℤ ℂ) =
      C (((Q.leadingCoeff : ℤ) : ℂ)) *
        ((Q.map (algebraMap ℤ ℂ)).roots.map (fun z : ℂ => X - C z)).prod := qc_factor_eq Q hQ
  have heval := congrArg (fun p : Polynomial ℂ => p.eval (0 : ℂ)) hfac
  calc
    (((Q.coeff 0 : ℤ) : ℂ)) = (Q.map (algebraMap ℤ ℂ)).eval (0 : ℂ) := by
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_zero (algebraMap ℤ ℂ)).symm
    _ = (C (((Q.leadingCoeff : ℤ) : ℂ)) *
          ((Q.map (algebraMap ℤ ℂ)).roots.map (fun z : ℂ => X - C z)).prod).eval (0 : ℂ) := by
      exact heval
    _ = (((Q.leadingCoeff : ℤ) : ℂ)) *
          ((rootMultiset Q).map (fun z : ℂ => (0 : ℂ) - z)).prod := by
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      rw [eval_prod_X_sub_C]
      rw [← rootMultiset_eq_roots Q]

/-- Norms in the zero-evaluation identity:
`‖Q(0)‖ = ‖lc‖ · ∏_{z ∈ roots} ‖z‖`. -/
lemma norm_eval_zero_factor (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    ‖(((Q.coeff 0 : ℤ) : ℂ))‖ =
      ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
        ((rootMultiset Q).map (fun z : ℂ => ‖z‖)).prod := by
  have hf := eval_zero_factor Q hQ
  calc
    ‖(((Q.coeff 0 : ℤ) : ℂ))‖
        = ‖(((Q.leadingCoeff : ℤ) : ℂ)) *
            ((rootMultiset Q).map (fun z : ℂ => (0 : ℂ) - z)).prod‖ := by rw [hf]
    _ = ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
          ‖((rootMultiset Q).map (fun z : ℂ => (0 : ℂ) - z)).prod‖ := by
          rw [Complex.norm_mul]
    _ = ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
          ((rootMultiset Q).map (fun z : ℂ => ‖z‖)).prod := by
          rw [norm_multiset_prod_eq]
          simp [Multiset.map_map]

/-- No root of a polynomial with nonzero constant term is zero. -/
lemma rootMultiset_ne_zero (Q : Polynomial ℤ) (hQ : Q ≠ 0) (hQ0 : Q.coeff 0 ≠ 0) :
    ∀ z ∈ rootMultiset Q, z ≠ 0 := by
  intro z hz hz0
  have hQc : Q.map (algebraMap ℤ ℂ) ≠ 0 := map_ne_zero_of_ne_zero Q hQ
  have hzero : (0 : ℂ) ∈ (Q.map (algebraMap ℤ ℂ)).roots := by
    rw [← rootMultiset_eq_roots Q]
    simpa [hz0] using hz
  have hroot : (Q.map (algebraMap ℤ ℂ)).eval (0 : ℂ) = 0 :=
    (Polynomial.mem_roots hQc).mp hzero
  have hc0 : ((Q.coeff 0 : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast hQ0
  apply hc0
  have heval : (Q.map (algebraMap ℤ ℂ)).eval (0 : ℂ) = ((Q.coeff 0 : ℤ) : ℂ) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_zero (algebraMap ℤ ℂ)
  rw [heval] at hroot
  exact hroot

/-- `log(∏_{z ∈ m} ‖z‖) = Σ_{z ∈ m} log‖z‖` for `m` avoiding zero. -/
lemma log_multiset_norm_prod (m : Multiset ℂ) (hm : ∀ z ∈ m, z ≠ 0) :
    Real.log ((m.map (fun z : ℂ => ‖z‖)).prod) =
      (m.map (fun z : ℂ => Real.log ‖z‖)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have ha : a ≠ 0 := hm a (by simp)
      have ht : ∀ z ∈ t, z ≠ 0 := fun z hz => hm z (by simp [hz])
      have hprod : ((t.map (fun z : ℂ => ‖z‖)).prod) ≠ 0 := by
        exact Multiset.prod_ne_zero (by
          intro hz
          rcases Multiset.mem_map.mp hz with ⟨w, hw1, hw2⟩
          exact ht w hw1 (norm_eq_zero.mp (by simpa [hw2])))
      simp [Multiset.prod_cons, Multiset.sum_cons,
        Real.log_mul (norm_ne_zero_iff.mpr ha) hprod, ih ht]

/-- (C3) Sum of root logarithms equals the log of the root-product ratio. -/
theorem root_product_log {Q : Polynomial ℤ} (hQ : Q ≠ 0) (hQ0 : Q.coeff 0 ≠ 0) :
    ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum =
      Real.log ‖(((Q.coeff 0 : ℤ) : ℂ))‖ - Real.log ‖((Q.leadingCoeff : ℤ) : ℂ)‖ := by
  have hz : ∀ z ∈ rootMultiset Q, z ≠ 0 := rootMultiset_ne_zero Q hQ hQ0
  have hnorm := norm_eval_zero_factor Q hQ
  have hlc : (((Q.leadingCoeff : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hprod0 : ((rootMultiset Q).map (fun z : ℂ => ‖z‖)).prod ≠ 0 := by
    exact Multiset.prod_ne_zero (by
      intro hm
      rcases Multiset.mem_map.mp hm with ⟨z, hz1, hz2⟩
      exact hz z hz1 (norm_eq_zero.mp (by simp [hz2])))
  have hlog : Real.log ‖(((Q.coeff 0 : ℤ) : ℂ))‖ =
      Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
        ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum := by
    calc
      Real.log ‖(((Q.coeff 0 : ℤ) : ℂ))‖
          = Real.log (‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
              ((rootMultiset Q).map (fun z : ℂ => ‖z‖)).prod) := by rw [hnorm]
      _ = Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
            Real.log (((rootMultiset Q).map (fun z : ℂ => ‖z‖)).prod) := by
            rw [Real.log_mul (norm_ne_zero_iff.mpr hlc) hprod0]
      _ = Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
            ((rootMultiset Q).map (fun z : ℂ => Real.log ‖z‖)).sum := by
            rw [log_multiset_norm_prod (rootMultiset Q) hz]
  linarith

end Submission.RootProductLog
