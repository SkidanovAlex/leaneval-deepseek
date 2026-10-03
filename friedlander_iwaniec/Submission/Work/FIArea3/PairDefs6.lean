/-
# `Submission.Work.FIArea3.PairDefs6` — the single analytic input of round-6 area 3

`PairSumBound6` is *FI* Lemma 10.1 in the weakest form in which (10.10) consumes it: an upper bound
for the `τ`-weighted pair sum over the *coprime* pairs of the polar box (5.14),

  `Σ_{(z₁,z₂)=1} ‖β_{z₁}‖‖β_{z₂}‖ (1 + τ(|Δ(z₁,z₂)|)) ≤ C·θ⁴N²(log N)^{2^19}`,

for every coefficient satisfying the paper's support-and-size hypothesis of Lemma 10.1
(`IsBoxCoeff`: supported in the polar box (5.14), free of primes `≤ P` (5.8), and `|β_z| ≤ τ(|z|²)`).

This is *implied* by the paper's Lemma 10.1, whose weight is the larger
`|β_{z₁}β_{z₂}|τ(|z₁|²)τ(|z₂|²)τ₃(Δ)`: for each pair `‖β_{z₁}‖‖β_{z₂}‖(1 + τ(|Δ|)) ≤ 2·|β_{z₁}β_{z₂}|
τ(|z₁|²)τ(|z₂|²)τ₃(Δ)` (using `‖β_z‖ ≤ τ(|z|²)` and `1 + τ(m) ≤ 2τ₃(m)`).  Its proof (Lemma 2.2
splitting `τ(|z₁|²)`, `τ(|z₂|²)`, `τ₃(Δ)` at small divisors, followed by the uniform count (10.9) of
`#{z₁,z₂ ∈ B : d ∣ Δ(z₁,z₂), d₁ ∣ |z₁|², d₂ ∣ |z₂|²} = O(θ⁴(N log N)²τ(dd₁d₂)/(dd₁d₂))` and the
divisor sums) is the one analytic input of area 3.

The statement is *weaker* than Lemma 10.1 in two independent ways: the `τ(|z₁|²)τ(|z₂|²)` factors
of the paper's weight are replaced by `1` (which is legitimate because the round-6 coefficient
(4.13)+(5.13)+(5.7) satisfies `‖β_z‖ ≤ 1` on its support rather than only `≤ τ(|z|²)`), and the
log-power is the one the paper's `Y`-bound produces.
-/
import Mathlib
import Submission.Work.FITop4.Areas6

set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The single analytic input of round-6 area 3** — *FI* Lemma 10.1 in the form in which the
corrected (10.10) consumes it: there is `C > 0` such that for every admissible datum and every
coefficient `β` of the polar box (5.14) with `(z,Π)=1` (5.8) and `|β_z| ≤ τ(|z|²)` (Lemma 10.1's
hypothesis),

  `Σ_{(z₁,z₂)=1} ‖β_{z₁}‖‖β_{z₂}‖(1 + τ(|Δ(z₁,z₂)|)) ≤ C·θ⁴N²(log N)^{2^19}`.

(The sum runs over the box `boxN Pa = gBox (radN Pa)`; `β` vanishes off the polar box.) -/
def PairSumBound6 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          else 0))
        ≤ C * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))

/-- **The weakest sufficient form of the input** — *FI* (10.10) needs exactly

  `Σ_{(z₁,z₂)=1} ‖β_{z₁}‖‖β_{z₂}‖(1 + τ(|Δ(z₁,z₂)|)) ≤ C·(τ⁻¹ + θ)θ³N²(log N)^{2^20−1}`,

because the §10 factor bounds give `‖D₀ − cMain6·T(β)‖ ≤ 28√M·θ·(log N)/√N · Σ`, and the right-hand
side of (10.10) is `C₃(τ⁻¹+θ)θ⁴√M N^{3/2}(log N)^{2^20}`.

This is implied by `PairSumBound6` (for `1 ≤ log N`): `θ⁴N²(log N)^{2^19} ≤ (τ⁻¹+θ)θ³N²(log N)^{2^20−1}`
is exactly `θ ≤ (τ⁻¹+θ)(log N)^{2^19−1}`.

**This statement is genuinely stronger than what the round-3 chain proves.**  `CoreBound`
(`FIArea3/Defs.lean`), which `avg_box_tau_r3` together with the joint average `JointBound`
implies, has the factor `(ϑ+θ)` in place of `(τ⁻¹+θ)`; but `τ⁻¹ ≤ ϑ(log x)^{−124}` and `θ ≤ ϑ`, so
`(ϑ+θ) ≥ (τ⁻¹+θ)·(log x)^{124}/2` — the round-3 conclusion is *always* weaker by at least
`(log x)^{124}/2`.  The `(τ⁻¹+θ)`-form is what round 4/6 consume, and it is what the paper's
Lemma 10.1 + (10.4) produce in the paper's parameter range `τ ≥ ϑ^{−2}(log x)^{2^20}` (10.11). -/
def PairSumWeak6 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          else 0))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)

end

end Work.FIArea3
