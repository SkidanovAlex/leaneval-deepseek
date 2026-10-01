/-
# The two halves of the accumulated Abel-error weight of the `S₃` computation

Namespace `Work.LinnikAreas.Density4.BzS3`.

The target `s3_error_sum_bound` (in `BzS3/s3_error_sum_bound.lean`) bounds the triple sum
`Σ_{q ≤ N/z} Σ_{r,t ≤ N/(qz)} W(q,r,t)·σ_{-1/2}(rt)`, where the weight `W = W_A + W_B` splits into

* the `√⌊N/(qrt)⌋`-part `W_A` (with both `log`-factors involving `⌊N/(qrt)⌋`), and
* the `√⌊max(z/t,z/r)⌋`-part `W_B` (with both `log`-factors involving `max(z/t,z/r)`).

`esbA`/`esbB` below are the corresponding inner `(r,t)`-sums at fixed `q`.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.Density4.BzS3

noncomputable section

/-- The `√⌊N/(qrt)⌋`-half of the accumulated Abel-error weight at fixed `q`. -/
def esbA (z N q : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
    (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
      * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ))

/-- The `√⌊max(z/t,z/r)⌋`-half of the accumulated Abel-error weight at fixed `q`. -/
def esbB (z N q : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
    (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
      * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ))

/-- The full weight at fixed `q` is the sum of the two halves. -/
lemma esbA_add_esbB (z N q : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        ((Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
          + Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ))))
      = esbA z N q + esbB z N q := by
  simp only [esbA, esbB, Finset.sum_add_distrib, add_mul]

/-- Nonnegativity of the `esbB` summands (the divisor sum is positive). -/
lemma esbB_nonneg (z N q : ℕ) : 0 ≤ esbB z N q := by
  rw [esbB]
  refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => ?_
  refine mul_nonneg ?_ (Finset.sum_nonneg fun d _ => ?_)
  · refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_) ?_ <;> positivity
  · positivity

/-- Nonnegativity of the `esbA` summands. -/
lemma esbA_nonneg (z N q : ℕ) : 0 ≤ esbA z N q := by
  rw [esbA]
  refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => ?_
  refine mul_nonneg ?_ (Finset.sum_nonneg fun d _ => ?_)
  · refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_) ?_ <;> positivity
  · positivity

end

end Work.LinnikAreas.Density4.BzS3
