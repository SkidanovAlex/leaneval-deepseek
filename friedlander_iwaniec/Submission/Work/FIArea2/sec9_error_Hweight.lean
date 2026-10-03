import Mathlib
import Submission.Work.FIArea2.sec9_error_of_pair
import Submission.Work.FIArea2.Gsum_bound

/-!
# (9.1) with the paper's weight `H(z₁,z₂)` of (9.2) kept

`Work.FIArea2.sec9_error_from_poisson` states display (9.1) with the right-hand side
`|z₁z₂|^{−1/2}·4·10⁶·τ(Δ)³|Δ|^{−1}·√M·log(2+δ^{−2})·H(z₁,z₂)`, where `H(z₁,z₂)` is the (9.2)
sum `Σ'_{(h₁,h₂)≠(0,0)}(z₁h₁²−z₂h₂², Δ)(1+h₁²H^{−2})^{−1}(1+h₂²H^{−2})^{−1}`.  What is *not*
there is the discharge of Lemma 8.1's arithmetic input `hG` while keeping that weight; the
companion `Work.FIArea2.sec9_error_of_pair` discharges `hG` but first *collapses* the weight by
`(Λ,Δ) ≤ |Δ|` and Euler–Maclaurin (`Work.FIArea2.sec9_error_explicit`), which loses a power of
`N` when summed over the `(z₁,z₂)`-pairs (the loss is exactly the lacunarity: the sum over `h` of
`(Λ,Δ)(1+h₁²H^{−2})^{−1}(1+h₂²H^{−2})^{−1}` is `≍ H²` only after the large common divisors of
`(Λ,Δ)` are grouped — see `NOTES.md` §22).  Since §9 must keep the gcd, (9.1) is needed in the
form below: `hG` discharged, weight kept, as a first-class object `Haver Pa z₁ z₂`.

The only new input is `Work.FIArea2.Gsum_bound`, i.e. Lemma 8.1 (8.5)
`|G(h₁,h₂)| ≤ 4τ(Δ)³(Λ,Δ)|Δ|^{−1}` under the standing hypotheses of the pair, which is used at
every frequency.
-/

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

/-- **The weight of (9.2)**, as the sum that the Poisson analysis of §6 actually produces: the
`h = (0,0)` term is removed and the remaining frequencies carry Lemma 7.1's weight
`(1+u_j²δ√M)^{−1}` with `u_j = h_j|Δz_{j'}|^{−1/2}`, `δ = |Δ|/|z₁z₂|` (so the weight is
`(1+h_j² secWeight_j)^{−1}` by `secFreq_sq_mul`), together with Lemma 8.1's gcd factor
`(Λ,Δ) = (z₁h₁² − z₂h₂², Δ)`.  This is `H(z₁,z₂)` of (9.2); `Work.FIArea2.tsum_gcd_weight_le`
bounds it by `|Δ|(1+π/√c₁)(1+π/√c₂)`, but §9 must *not* do that before the summation over the
pairs (see the module doc string). -/
def Haver (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
    (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
      * (1 + (Work.FIArea2.secFreq₁ z1 z2 h.1) ^ 2
          * Real.sqrt (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) * Real.sqrt Pa.M)⁻¹
      * (1 + (Work.FIArea2.secFreq₂ z1 z2 h.2) ^ 2
          * Real.sqrt (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) * Real.sqrt Pa.M)⁻¹)

end

end Work.FIArea2
