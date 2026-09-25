import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Region II: the Abel lower bound for `Σ_{n<p≤z} 1/p²`

This module fixes the vocabulary of the "region A" (`30000 ≤ ξ < 10^5`) margin
estimate `caC1_add_caNet2_lower_A`.

For integers `173 ≤ n ≤ z ≤ 10^5` the Abel identity
`Σ_{n<p≤z} 1/p² = θ z / (z² log z) − θ n / (n² log n) + ∫_n^z ((2 log t + 1)/(t³ log²t)) θ t`
(`Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel`) is turned into a fully explicit
lower bound by

* `θ z ≥ 96/100 · z`  (Chebyshev-type table bound on `[1530, 10^5]`);
* `θ n ≤ n − (64/100)√n`  (certified deficit bound, `173 ≤ n ≤ 501`);
* on `(n,501]`: `θ t ≥ (t−1) − (189/100)√t`  (certified deficit bound at integers);
* on `(501,z]`: `θ t ≥ t − (23/10)√t`  (the hypothesis `hθ` of the main lemma),

and the three elementary integral estimates for the kernel
`h t = (2 log t + 1)/(t³ log² t)` (with `u t = 1/(t log t)`, `χ t = (2 + 1/log t)/log t`):

* `∫_a^b h t · t dt ≥ 2(u a − u b) − (u a − u b)/(log a + 1)`;
* `∫_a^b h t dt ≤ χ a / 2 · (a⁻² − b⁻²)`;
* `∫_a^b h t · √t dt ≤ χ a · (2/3) · (a^{-3/2} − b^{-3/2})`.

Splitting the integral at `501` gives `Σ ≥ abJ z − abA n`.
-/

namespace Work.RHContract.A.RegionII

noncomputable section

/-- `u(t) = 1/(t log t)`, the antiderivative weight of the Abel kernel. -/
def uAb (t : ℝ) : ℝ := 1 / (t * Real.log t)

/-- `χ(t) = (2 + 1/log t)/log t`, the coefficient of the two remainder estimates. -/
def chAb (t : ℝ) : ℝ := (2 + 1 / Real.log t) / Real.log t

/-- `abA n`: the part of the Abel lower bound coming from the range `(n, 501]`
(a *loss*: it is subtracted from `abJ`). -/
def abA (n : ℕ) : ℝ :=
  (1 - (64 / 100) / Real.sqrt n) / ((n : ℝ) * Real.log n)
    - 2 * (uAb (n : ℝ) - uAb 501) + (uAb (n : ℝ) - uAb 501) / (Real.log n + 1)
    + chAb (n : ℝ) / 2 * (1 / (n : ℝ) ^ 2 - 1 / 501 ^ 2)
    + (189 / 100) * chAb (n : ℝ) * (2 / 3)
        * (1 / ((n : ℝ) * Real.sqrt n) - 1 / (501 * Real.sqrt 501))

/-- `abJ z`: the part of the Abel lower bound coming from the range `(501, z]`. -/
def abJ (z : ℕ) : ℝ :=
  (96 / 100) / ((z : ℝ) * Real.log z)
    + 2 * (uAb 501 - uAb (z : ℝ)) - (uAb 501 - uAb (z : ℝ)) / (Real.log 501 + 1)
    - (23 / 10) * chAb 501 * (2 / 3)
        * (1 / (501 * Real.sqrt 501) - 1 / ((z : ℝ) * Real.sqrt z))

/-- The explicit lower bound for `Σ_{n<p≤z, p prime} 1/p²`. -/
def abS (n z : ℕ) : ℝ := abJ z - abA n

end

end Work.RHContract.A.RegionII
