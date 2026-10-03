/-
# The arithmetic sum `G(h₁,h₂)` of *FI* §8, and the gcd `(Λ,Δ)` of §9

*FI* (6.10) defines the exponential sum

  `G(h₁,h₂) = |Δ|⁻¹ ∑_{γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|)} e((γ₁h₁ + γ₂h₂)/|Δ|)`,

which is what the Poisson step (6.9) produces, and §9 (9.4) puts `Λ = z₁h₁² − z₂h₂²`.  The bound
(8.5) of Lemma 8.1 is then `|G(h₁,h₂)| ≤ 4τ(Δ)³·(Λ,Δ)/|Δ|`, where `(Λ,Δ)` is the largest
**rational** integer `d ∣ |Δ|` dividing both components of the Gaussian integer `Λ` (this is what
§9 uses: "`Λ(r₁,r₂) ≡ Λ(s₁,s₂) ≡ 0 (mod d)`" for the real and imaginary parts separately).  The
identifications are recorded here as definitions, so that (8.5) can be stated in this vocabulary.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(6.10)**, the arithmetic sum: `G(h₁,h₂) = |Δ|⁻¹ ∑_{γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|)}
e((γ₁h₁+γ₂h₂)/|Δ|)`, `e(x) = exp(2πix)`, the sum running over the pairs of residues
`(γ₁,γ₂) ∈ [0,|Δ|)²` satisfying the two congruences (6.5).  (`Δ = 0` gives `0`.) -/
def Gsum (z1 z2 : GaussianInt) (h1 h2 : ℤ) : ℂ :=
  (((Work.FIPlan.absDelta z1 z2 : ℝ))⁻¹) *
    ∑ γ1 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
      ∑ γ2 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
        (if (γ1 ^ 2 * z2.re - γ2 ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
            (γ1 ^ 2 * z2.im - γ2 ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
          then Complex.exp (2 * Real.pi * Complex.I
            * (((γ1 : ℤ) * h1 + (γ2 : ℤ) * h2 : ℤ) : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
          else 0)

/-- **(9.4)**: `Λ(z₁,z₂) = z₁h₁² − z₂h₂²`. -/
def Lam (z1 z2 : GaussianInt) (h1 h2 : ℤ) : GaussianInt :=
  z1 * (h1 ^ 2 : ℤ) - z2 * (h2 ^ 2 : ℤ)

/-- The largest rational integer `d ∣ |Δ|` dividing both components of `Λ = z₁h₁² − z₂h₂²` — the
`(Λ,Δ)` of (9.5)–(9.6). -/
def gcdDelta (z1 z2 : GaussianInt) (h1 h2 : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd ((Lam z1 z2 h1 h2).re.natAbs) ((Lam z1 z2 h1 h2).im.natAbs))
    (Work.FIPlan.absDelta z1 z2)

end

end Work.FIArea2
