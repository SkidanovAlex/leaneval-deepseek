import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs

/-!
# `FIArea2/R6/WCDefs` — the weighted primitive-pair count at modulus `c`

For the sharp per-modulus reduction `ndCount_bound_sq` we expand the `gcd(d, ·)` weight of the
primitive-direction sum `Star` over the divisors of `d`:

  `Star d r X Y = Σ_{c ∣ d} φ(c) · WC c r X Y`,

where `WC c r X Y` is the weighted count of **primitive** pairs `(w₁,w₂) ∈ (±[1,r]²)` with
`c ∣ w₁h₁² - w₂h₂² ≠ 0`, the weight being `1/max(|w₁|,|w₂|)`, summed over the `(h₁,h₂)`-box.

This is the exact analogue of the paper's

  `L(r₁,r₂) ≪ Σ_{q ≤ H} τ(q)^c q^{-2} N(r₁,r₂;q)`   (Friedlander–Iwaniec, (9.7)),

the modulus playing the role of `q`; `WC` is the "weighted primitive count at modulus `c`".
-/

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The weighted primitive-pair count at modulus `c`: sum over the `(h₁,h₂)`-box and over
primitive `(w₁,w₂) ∈ (±[1,r])²` with `c ∣ w₁h₁² - w₂h₂² ≠ 0` of the weight `1/max(|w₁|,|w₂|)`. -/
def WC (c r X Y : ℕ) : ℝ :=
  ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r,
    (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
        ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
      then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0)

end

end Work.FIArea2.R6
