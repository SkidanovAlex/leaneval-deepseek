/-
# `FIArea2/R6/ndCountDefs` — auxiliary vocabulary for `ndCount_bound`

The definitions used by the corrected route to `ndCount_bound`:

* `WcFun c r X Y`: the weighted primitive-direction sum at modulus `c`,
  `Σ_{h₁,h₂} Σ_{(a,b) primitive, a,b ≠ 0, |a|,|b| ≤ r, c ∣ ah₁² - bh₂² ≠ 0} 1/max(|a|,|b|)`;
* `gcdBox c X Y = Σ_{h₁,h₂} gcd(c, h₁², h₂²)`;
* `StarSum d r X Y`: the primitive weighted sum with `gcd(d, ah₁²-bh₂²)`,
  the exact upper bound produced by the `(x,y) = t·(a,b)` reduction of `ndCount`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The weighted primitive-direction sum at modulus `c` over the `(h₁,h₂)`-box,
summed over `(h₁,h₂)`:  `Σ_{h₁,h₂} Σ_{(a,b) primitive, a,b ≠ 0, |a|,|b| ≤ r, c ∣ ah₁²-bh₂² ≠ 0}
1/max(|a|,|b|)`. -/
def WcFun (c r X Y : ℕ) : ℝ :=
  ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ a ∈ zPz r, ∑ b ∈ zPz r,
    (if Int.gcd a b = 1 ∧ (c : ℤ) ∣ a * h1 ^ 2 - b * h2 ^ 2
        ∧ a * h1 ^ 2 - b * h2 ^ 2 ≠ 0
      then (1 : ℝ) / ((max a.natAbs b.natAbs : ℕ) : ℝ) else 0)

/-- `Σ_{(h₁,h₂) ∈ ([-X,X]\{0}) × ([-Y,Y]\{0})} gcd(c, h₁², h₂²)`. -/
def gcdBox (c X Y : ℕ) : ℕ :=
  ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, Nat.gcd (Nat.gcd c (h1 ^ 2).natAbs) (h2 ^ 2).natAbs

/-- The primitive weighted sum `(★)` produced by the `(x,y) = t·(a,b)` reduction:
`Σ_{h₁,h₂} Σ_{(a,b) primitive, a,b ≠ 0, |a|,|b| ≤ r, ah₁² ≠ bh₂²} gcd(d, ah₁²-bh₂²)/max(|a|,|b|)`. -/
def StarSum (d r X Y : ℕ) : ℝ :=
  ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ a ∈ zPz r, ∑ b ∈ zPz r,
    (if Int.gcd a b = 1 ∧ a * h1 ^ 2 - b * h2 ^ 2 ≠ 0
      then (Nat.gcd (a * h1 ^ 2 - b * h2 ^ 2).natAbs d : ℝ)
        / ((max a.natAbs b.natAbs : ℕ) : ℝ) else 0)

end

end Work.FIArea2.R6
