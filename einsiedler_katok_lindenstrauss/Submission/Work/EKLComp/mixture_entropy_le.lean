import Mathlib
import Submission.Work.EKLComp.Core

/-!
# Entropy of a two-point mixture

For two probability vectors `q r : ι → ℝ` on a finite type and weights `p, p' ≥ 0`
with `p + p' = 1`, the Shannon entropy `H x = ∑ i, Real.negMulLog (x i)` satisfies

  `H (p • q + p' • r) ≤ p * H q + p' * H r + log 2`.

The constant `log 2` is optimal (e.g. `q = δ₀`, `r = δ₁`, `p = p' = 1/2`).

The proof goes through the pointwise subadditivity of `Real.negMulLog`
(`negMulLog (a + b) ≤ negMulLog a + negMulLog b` for `a, b ≥ 0`, here available in
`Submission.Work.EKLComp.Core`) together with the multiplication identity
`Real.negMulLog_mul : negMulLog (x * y) = y * negMulLog x + x * negMulLog y`,
which turns the two sums `∑ i, negMulLog (p * q i)` and `∑ i, negMulLog (p' * r i)`
into `negMulLog p + p * ∑ i, negMulLog (q i)` and `negMulLog p' + p' * ∑ i, negMulLog (r i)`.
It remains to bound the binary entropy `negMulLog p + negMulLog p' ≤ log 2`, which is
Mathlib's `Real.binEntropy_le_log_two`.
-/

namespace Work.EKLComp

open Finset

theorem mixture_entropy_le {ι : Type*} [Fintype ι] (p p' : ℝ) (q r : ι → ℝ)
    (hp : 0 ≤ p) (hp' : 0 ≤ p') (hpw : p + p' = 1)
    (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hq1 : ∑ i, q i = 1) (hr1 : ∑ i, r i = 1) :
    ∑ i, Real.negMulLog (p * q i + p' * r i) ≤
      p * (∑ i, Real.negMulLog (q i)) + p' * (∑ i, Real.negMulLog (r i)) + Real.log 2 := by
  -- each coordinate of a probability vector is at most `1`
  have hq_le : ∀ i, q i ≤ 1 := fun i => by
    simpa [hq1] using Finset.single_le_sum (f := q) (fun j _ => hq j) (Finset.mem_univ i)
  have hr_le : ∀ i, r i ≤ 1 := fun i => by
    simpa [hr1] using Finset.single_le_sum (f := r) (fun j _ => hr j) (Finset.mem_univ i)
  -- Step 1: pointwise subadditivity of `negMulLog`
  have hsub : ∑ i, Real.negMulLog (p * q i + p' * r i)
      ≤ ∑ i, Real.negMulLog (p * q i) + ∑ i, Real.negMulLog (p' * r i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ =>
      Core.negMulLog_add_le (mul_nonneg hp (hq i)) (mul_nonneg hp' (hr i)) ?_
    nlinarith [hq_le i, hr_le i]
  -- Step 2: split each sum using `negMulLog_mul`
  have hA : ∑ i, Real.negMulLog (p * q i)
      = Real.negMulLog p + p * ∑ i, Real.negMulLog (q i) := by
    rw [Finset.sum_congr rfl (fun i _ => Real.negMulLog_mul p (q i))]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq1]
    ring
  have hB : ∑ i, Real.negMulLog (p' * r i)
      = Real.negMulLog p' + p' * ∑ i, Real.negMulLog (r i) := by
    rw [Finset.sum_congr rfl (fun i _ => Real.negMulLog_mul p' (r i))]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hr1]
    ring
  -- Step 3: the binary entropy bound
  have hbin : Real.negMulLog p + Real.negMulLog p' ≤ Real.log 2 := by
    have hp'eq : p' = 1 - p := by linarith
    rw [hp'eq, ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub p]
    exact Real.binEntropy_le_log_two
  linarith [hsub, hA, hB, hbin]

end Work.EKLComp
