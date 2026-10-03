/-
# `Submission.Work.FIArea3.PairBracketDefs` — the double divisor sums of the polar-box
τ-average

`Work.FIArea3.pairBracketPrim` bounds
`Σ_{z₂ ∈ polar box} τ(|z₂|²)·τ(|Δ(z₁,z₂)|)`.  After

* splitting both `τ`'s with FI Lemma 2.2 (`k = 4`),
* rearranging (`JointCount.joint_double_sum_bound_aux`), and
* bounding the per-`(d,e)` count with `Work.FIArea3.jointCountNoBox`
  (`# ≤ π·u²·τ(d)·gcd(d,e)/(d·e) + 80·u·τ(d)/√d + τ(d)`, `u = θ√N`),

the sum is controlled by the three explicit divisor sums defined here, with `τ(n) = n.divisors.card`:

  `dsum1 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸ gcd(d,e)/(d·e)`,
  `dsum2 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸ / √d`,
  `dsum3 K₁ K₂ = Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)⁹ τ(e)⁸`.

These are elementary divisor sums; they are bounded in `PairBracketArith`.
-/
import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le

open Finset
open scoped BigOperators

namespace Work.FIArea3

noncomputable section

/-- `Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)^9 τ(e)^8 gcd(d,e)/(d e)` — the main term of the polar-box
τ-average after the `jointCountNoBox` count. -/
def dsum1 (K1 K2 : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
    (Work.FIArea2.tauR d) ^ (9 : ℕ) * (Work.FIArea2.tauR e) ^ (8 : ℕ)
      * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))

/-- `Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)^9 τ(e)^8 / √d` — the "linear" error term. -/
def dsum2 (K1 K2 : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
    (Work.FIArea2.tauR d) ^ (9 : ℕ) * (Work.FIArea2.tauR e) ^ (8 : ℕ) / Real.sqrt (d : ℝ)

/-- `Σ_{d ≤ K₁} Σ_{e ≤ K₂} τ(d)^9 τ(e)^8` — the "constant" error term. -/
def dsum3 (K1 K2 : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
    (Work.FIArea2.tauR d) ^ (9 : ℕ) * (Work.FIArea2.tauR e) ^ (8 : ℕ)

end

end Work.FIArea3
