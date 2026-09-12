import Submission.SqueezeCore
import Mathlib.Tactic

/-! # Child task: pointwise log-product identity on the good set.

Prove `log_tupleF_eq_totalLog` (mirror of `Submission.SqueezeCore`'s lemma).
Add helper lemmas **in this file**, namespace `Submission.SqzLogProd`.
Definitions (in `Submission.SqueezeCore`):
`GoodTuple d R x`, `tupleF d n R x = (∏ k, weight(xk)^n·|aeval(xk) R|)·pairProd d x`,
`totalLog d n R x = (∑ k, coordLog n R (x k)) + pairLog d x`,
`coordLog n R x = log|aeval x R| + n·log(weight x)`,
`pairLog d x = ∑ i, ∑ j ∈ filter(i<j), log|x_i − x_j|`,
`pairProd d x` (MinkBox) = `∏ i, ∏ j ∈ filter(i<j), |x_i − x_j|`.

## What to prove

    log_tupleF_eq_totalLog {d n} (R) {x} (hx : GoodTuple d R x) :
        Real.log (tupleF d n R x) = totalLog d n R x

On good tuples every factor is strictly positive: `weight > 0`
(`Submission.WeightedNorm.weight_pos`), `|aeval(xk) R| > 0` (hx.2.1), and for
`i < j`, `|x_i − x_j| > 0` (distinct, hx.2.2).  Then:
1. log of the big product = sum of logs (Real.log_prod over the two Finset
   layers) + log of product over k of w^n·|R| (Real.log_mul, and
   `Real.log (a ^ n) = n · Real.log a` via `Real.log_pow`, `pow_ne_zero`);
2. `Real.log (weight x) = logPotential ...` = you may use it directly via the
   definition of coordLog (note coordLog uses `Real.log (weight muSerre x)` —
   combine with `Submission.SqueezeCore.log_weight_eq_potential` if needed);
3. `(weight x) ^ n = Real.exp (n · log (weight x))`-style steps if helpful
   (`Real.exp_log` / `Real.log_exp`), or use `Real.log_pow`.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real BigOperators ENNReal Topology

namespace Submission.SqzLogProd

open Submission.SqueezeCore
open Submission.MinkBox
open Submission.Contracts
open Submission.SerreExample
open Submission.WeightedNorm

/-- The logarithm of a product of strictly positive reals is the sum of the
logarithms (finite product version with positivity hypotheses). -/
private lemma log_prod_pos {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    Real.log (∏ i ∈ s, f i) = ∑ i ∈ s, Real.log (f i) := by
  rw [Real.log_prod]
  intro i hi
  exact ne_of_gt (hf i hi)

lemma log_tupleF_eq_totalLog {d n : ℕ} (R : Polynomial ℤ) {x : Fin d → ℝ}
    (hx : GoodTuple d R x) :
    Real.log (tupleF d n R x) = totalLog d n R x := by
  classical
  rcases hx with ⟨hI, hR, hinj⟩
  -- Per-coordinate factor A k = w(x_k)^n · |R(x_k)|
  let A : Fin d → ℝ := fun k => (weight muSerre (x k)) ^ n * |Polynomial.aeval (x k) R|
  have hwpos (k : Fin d) : 0 < weight muSerre (x k) := weight_pos muSerre (x k)
  have hApos (k : Fin d) : 0 < A k := by
    dsimp [A]
    exact mul_pos (pow_pos (hwpos k) n) (abs_pos.mpr (hR k))
  have hlogA (k : Fin d) : Real.log (A k) = coordLog n R (x k) := by
    dsimp [A]
    calc
      Real.log ((weight muSerre (x k)) ^ n * |Polynomial.aeval (x k) R|)
          = Real.log ((weight muSerre (x k)) ^ n) + Real.log (|Polynomial.aeval (x k) R|) := by
              apply Real.log_mul
              · exact pow_ne_zero n (ne_of_gt (hwpos k))
              · exact abs_ne_zero.mpr (hR k)
      _ = (n : ℝ) * Real.log (weight muSerre (x k)) + Real.log (|Polynomial.aeval (x k) R|) := by
              rw [Real.log_pow]
      _ = coordLog n R (x k) := by
              rw [coordLog]
              ring
  -- log of the product over k
  have hsumLog : Real.log (∏ k : Fin d, A k) = ∑ k : Fin d, coordLog n R (x k) := by
    calc
      Real.log (∏ k : Fin d, A k) = ∑ k : Fin d, Real.log (A k) := by
          rw [log_prod_pos]
          intro k hk
          exact hApos k
      _ = ∑ k : Fin d, coordLog n R (x k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hlogA k
  -- pair positivity and log of pairProd
  have hpairpos (i j : Fin d) (hij : i < j) : 0 < |x i - x j| := by
    exact abs_pos.mpr (sub_ne_zero.mpr (hinj.ne (ne_of_lt hij)))
  have hpairProd_pos : 0 < MinkBox.pairProd d x := by
    dsimp [MinkBox.pairProd]
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact hpairpos i j (Finset.mem_filter.mp hj).2
  have hpairlog : Real.log (MinkBox.pairProd d x) = pairLog d x := by
    dsimp [MinkBox.pairProd, pairLog]
    calc
      Real.log (∏ i : Fin d,
          ∏ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), |x i - x j|)
          = ∑ i : Fin d,
              Real.log (∏ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), |x i - x j|) := by
              rw [log_prod_pos]
              intro i hi
              apply Finset.prod_pos
              intro j hj
              exact hpairpos i j (Finset.mem_filter.mp hj).2
      _ = ∑ i : Fin d,
              ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), Real.log (|x i - x j|) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [log_prod_pos]
              intro j hj
              exact hpairpos i j (Finset.mem_filter.mp hj).2
  calc
    Real.log (tupleF d n R x)
        = Real.log ((∏ k : Fin d, A k) * MinkBox.pairProd d x) := by
            simp [tupleF, A]
    _ = Real.log (∏ k : Fin d, A k) + Real.log (MinkBox.pairProd d x) := by
            rw [Real.log_mul]
            · exact ne_of_gt (Finset.prod_pos (s := (Finset.univ : Finset (Fin d)))
                (f := A) (by intro k hk; exact hApos k))
            · exact ne_of_gt hpairProd_pos
    _ = (∑ k : Fin d, coordLog n R (x k)) + Real.log (MinkBox.pairProd d x) := by
            rw [hsumLog]
    _ = (∑ k : Fin d, coordLog n R (x k)) + pairLog d x := by
            rw [hpairlog]
    _ = totalLog d n R x := by
            rfl

end Submission.SqzLogProd
