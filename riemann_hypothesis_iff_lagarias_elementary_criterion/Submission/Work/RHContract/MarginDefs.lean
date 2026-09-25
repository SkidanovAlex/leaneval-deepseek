import Submission.Work.RHContract.Defs
import Mathlib.NumberTheory.Chebyshev

/-!
# `Work.RHContract.MarginDefs` — the four explicit quantities of the margin lemma

ROUTE_LEAD §2.3 proves that for a colossally abundant number `N = N_ε` with largest prime
`x = ξ(ε) ≥ 1530`,

`Δ(N) := logloglog N − log(σ(N)/N) ≥ J(x) + C₁ + Net₂ − W − K₃`,

where `J = psiTail` and the four explicit quantities are

* `caC1  ε = Σ_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³))`   (the `k = 1` excesses),
* `caNet2 ε = Σ_{√ξ < p ≤ ξ₂} (c·log p − 1/(2p(p−1)))`  (net gain of the `k = 2` level),
* `caW   ε = log log ξ + (ψ ξ − ξ)/(ξ log ξ) − log log ψ ξ`  (the `log log` correction),
* `caK3  ε = Σ_{p ≤ √ξ, a_p > e_p} max(0, p^{−(e_p+1)}/((e_p+1)(1−1/p)) − c·log p)`
  (the losses of the deeper levels `k ≥ 3`),

with `c = (1 − 3/√ξ)/(ψ(ξ) log ψ(ξ))`, `e_p = ⌊log ξ / log p⌋`, and
`ξ₂ = max{p : a_p ≥ 2}` (`caXi2`).  The statement `ca_margin_lower` of these quantities is
ROUTE_LEAD's Lemma M.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

namespace Margin

/-- `ξ₂(ε)`: the largest prime whose colossally abundant exponent is `≥ 2`.  (It is `0` if
there is none.) -/
def caXi2 (ε : ℝ) : ℕ :=
  ((Work.RHPlan.caSupport ε).filter (fun p : ℕ => 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊)).sup id

/-- The exponent `e_p = ⌊log ξ / log p⌋` of `p` in `lcm(1..ξ)`. -/
def caExpFloor (ε : ℝ) (p : ℕ) : ℕ := Nat.log p ⌊(Work.RHPlan.caXi ε : ℝ)⌋₊

/-- `c(ε) = (1 − 3/√ξ)/(ψ(ξ) · log ψ(ξ))`, the per-level gain coefficient of ROUTE_LEAD
§2.3. -/
def caC (ε : ℝ) : ℝ :=
  (1 - 3 / Real.sqrt (Work.RHPlan.caXi ε : ℝ)) /
    (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) *
      Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)))

/-- `C₁`: the sum of the `k = 1` excesses over the primes above `ξ₂`. -/
def caC1 (ε : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊(Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q : ℕ => caXi2 ε < q),
      (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3))

/-- `Net₂`: the net gain of the primes `√ξ < p ≤ ξ₂`. -/
def caNet2 (ε : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE (caXi2 ε)).filter
        (fun q : ℕ => ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ < q),
      (caC ε * Real.log (p : ℝ) - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)))

/-- `K₃`: the losses of the primes `p ≤ √ξ` whose exponent exceeds `e_p`. -/
def caK3 (ε : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q : ℕ => caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊),
      (max 0 ((p : ℝ) ^ (-(((caExpFloor ε p : ℝ) + 1))) /
               (((caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
             - caC ε * Real.log (p : ℝ)))

/-- `W`: the `log log` correction `log log ξ + v/L − log log ψ(ξ)`, `v = (ψ ξ − ξ)/ξ` and
`L = log ξ`. -/
def caW (ε : ℝ) : ℝ :=
  Real.log (Real.log (Work.RHPlan.caXi ε : ℝ))
    + (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)) /
        ((Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
    - Real.log (Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)))

end Margin

end

end Work.RHContract
