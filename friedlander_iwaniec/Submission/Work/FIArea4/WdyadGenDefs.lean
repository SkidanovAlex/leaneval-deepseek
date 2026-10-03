import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The class sum of `Wdyad` over an arbitrary modulus interval `(lo, hi]`:
`∑_{lo<d≤hi} ∑_{a<d} γ a d · Mentry d a r s`. -/
def TZbox (lo hi : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc lo hi, ∑ a ∈ Finset.range d, γ a d * Mentry d a r s

/-- The `e`-th stratum of the coefficients: `γ^{(e)}_{a d} = [ (a,d)=1 ] γ_{ea,ed}`. -/
def gamE (γ : ℕ → ℕ → ℂ) (e : ℕ) : ℕ → ℕ → ℂ :=
  fun a d => if Nat.Coprime a d then γ (e * a) (e * d) else 0

/-- The `e`-th stratum projection of the coefficients: `[gcd a d = e] γ_{a d}`. -/
def gLift (γ : ℕ → ℕ → ℂ) (e : ℕ) : ℕ → ℕ → ℂ :=
  fun a d => if Nat.gcd a d = e then γ a d else 0

/-- The bracket of `hunit` (with a real modulus parameter). -/
def bracket (D : ℝ) (R S : ℕ) (ε : ℝ) : ℝ :=
  D ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + (((R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)
        + D * Real.sqrt ((R : ℝ) * (S : ℝ))
        + D * (min R S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε))

/-- The per-stratum majorant produced by the dyadic covering: four `bracket` evaluations at the
(modulus, `s`-box) pairs `(⌊D/e⌋,⌊S/e⌋)`, `(⌊D/e⌋,2⌊S/e⌋)`, `(2⌊D/e⌋,⌊S/e⌋)`, `(2⌊D/e⌋,2⌊S/e⌋)`. -/
def KE (D R S e : ℕ) (ε : ℝ) : ℝ :=
  bracket ((D / e : ℕ) : ℝ) R (S / e) ε + bracket ((D / e : ℕ) : ℝ) R (2 * (S / e)) ε
    + bracket (2 * ((D / e : ℕ) : ℝ)) R (S / e) ε
    + bracket (2 * ((D / e : ℕ) : ℝ)) R (2 * (S / e)) ε

end

end Work.FIArea4
